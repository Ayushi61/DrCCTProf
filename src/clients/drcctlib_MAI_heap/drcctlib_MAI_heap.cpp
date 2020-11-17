/* 
 *  Copyright (c) 2020 Xuhpclab. All rights reserved.
 *  Licensed under the MIT License.
 *  See LICENSE file for more information.
 */

#include <cstddef>

#include <map>
#include <set>
#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"
#include "drwrap.h"
#include "shadow_memory.h"
#include <utility>
#include <vector>
#include <algorithm>
#define FUNC_FOOTPRINT
//#define INSTR_FOOTPRINT
#define DRCCTLIB_PRINTF(format, args...) \
    DRCCTLIB_PRINTF_TEMPLATE("drcctlib_MAI_heap", format, ##args)
#define DRCCTLIB_EXIT_PROCESS(format, args...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("drcctlib_MAI_heap.cpp", format, \
                                          ##args)
#define THREAD_ROOT_SHARDED_CALLER_CONTEXT_HANDLE 1
#define MAX_CLIENT_CCT_PRINT_DEPTH 10
int tls_idx;
static file_t gTraceFile;
enum {
    INSTRACE_TLS_OFFS_BUF_PTR,
    INSTRACE_TLS_COUNT, /* total number of TLS slots allocated */
};
static reg_id_t tls_seg;
static uint tls_offs;
#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base, type, offs) *(type **)TLS_SLOT(tls_base, offs)
#define MINSERT instrlist_meta_preinsert
#ifdef ARM_CCTLIB
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT
#else
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT32
#endif

#ifdef WINDOWS
#    define IF_WINDOWS_ELSE(x, y) x
#else
#    define IF_WINDOWS_ELSE(x, y) y
#endif
#define MALLOC_ROUTINE_NAME IF_WINDOWS_ELSE("HeapAlloc", "malloc")
#define FREE_ROUTINE_NAME IF_WINDOWS_ELSE("Free", "free")
static uint malloc_oom;
static size_t max_malloc;
static void *max_lock;
typedef struct _mem_ref_t {
    app_pc addr;
    size_t size;
    int32_t read_write;
} mem_ref_t;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
} per_thread_t;
//structure to record context handle and rw

#define TLS_MEM_REF_BUFF_SIZE 100
#define RED_SZ 50
std::map<app_pc, size_t> MAI;
std::map<app_pc,context_handle_t> MAI_ctx;
std::set<int64_t> ctx_red_malloc;
int cnt=0;
// client want to do
void
eachMemAccess(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref)
{
    // add online analysis here

    size_t instr_size=ref->size;
    app_pc init_addr=ref->addr;
    app_pc it;
    int i=0;
    std::map<app_pc,size_t>::iterator MAI_it=MAI.find(init_addr);
    for(app_pc i=init_addr;i<init_addr+instr_size;i++)
    {
        if(MAI_it!=MAI.end())
        {
            size_t sz=MAI_it->second;
            if(i>MAI_it->first+sz){
                std::map<app_pc,context_handle_t>::iterator ctx_it=MAI_ctx.find(init_addr);
                context_handle_t mai_ctx=ctx_it->second;
                // dr_fprintf(gTraceFile)
                ctx_red_malloc.insert((((int64_t)mai_ctx)<<32) | (((int64_t)cur_ctxt_hndl)<<32)>>32);
            }
        } 
    }
}
// dr clean call Memory
void
InsertCleancall(int32_t slot,int32_t num)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            eachMemAccess(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
        }
    }

    
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
    
}

// insert
static void
InstrumentMem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref)
{
    /* We need two scratch registers */
    reg_id_t reg_mem_ref_ptr, free_reg;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &free_reg) !=
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_reserve_register != DRREG_SUCCESS");
    }
    if (!drutil_insert_get_mem_addr(drcontext, ilist, where, ref, free_reg,
                                    reg_mem_ref_ptr)) {
        MINSERT(ilist, where,
                XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                      OPND_CREATE_CCT_INT(0)));
    }
    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    // store mem_ref_t->addr
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr)),
                opnd_create_reg(free_reg)));

    // store mem_ref_t->size
#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
#endif
#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
#endif
    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    /* Restore scratch registers */
    if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, free_reg) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_unreserve_register != DRREG_SUCCESS");
    }
}

// analysis
void 
InstrumentInsCallback(void *drcontext, instr_instrument_msg_t *instrument_msg)
{


    instrlist_t *bb = instrument_msg->bb;
    instr_t *instr = instrument_msg->instr;
    int32_t slot = instrument_msg->slot;
    int num = 0;
    for (int i = 0; i < instr_num_srcs(instr); i++) {
        if (opnd_is_memory_reference(instr_get_src(instr, i))) {
            num++;
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i));
        }
    }
    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_memory_reference(instr_get_dst(instr, i))) {
            num++;
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i));
        }
    }
    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 2,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num));

}

static void
ClientThreadStart(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)dr_thread_alloc(drcontext, sizeof(per_thread_t));
    if (pt == NULL) {
        DRCCTLIB_EXIT_PROCESS("pt == NULL");
    }
    drmgr_set_tls_field(drcontext, tls_idx, (void *)pt);

    pt->cur_buf = dr_get_dr_segment_base(tls_seg);
    pt->cur_buf_list =
        (mem_ref_t *)dr_global_alloc(TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

static void
ClientThreadEnd(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));
}

static void
ClientInit(int argc, const char *argv[])
{
    #ifdef ARM_CCTLIB
    char name[MAXIMUM_PATH] = "arm.drcctlib_MAI_heap.out.";
#else
    char name[MAXIMUM_PATH] = "x86.drcctlib_MAI_heap.out.";
#endif

    gethostname(name + strlen(name), MAXIMUM_PATH - strlen(name));
    pid_t pid = getpid();
    sprintf(name + strlen(name), "%d", pid);
    DRCCTLIB_PRINTF("Creating log file at:%s", name);
    gTraceFile = dr_open_file(name, DR_FILE_WRITE_OVERWRITE | DR_FILE_ALLOW_LARGE);
    DR_ASSERT(gTraceFile != INVALID_FILE);
    // print the arguments passed
    dr_fprintf(gTraceFile, "\n");
    for (int i = 0; i < argc; i++) {
        dr_fprintf(gTraceFile, "%d %s ", i, argv[i]);
    }
    dr_fprintf(gTraceFile, "\n");
    dr_fprintf(gTraceFile, " ===========init========\n");
}
/*
bool cmp(std::pair<int64_t, int64_t>& a, 
                 std::pair<int64_t, int64_t>& b) 
{ 
        return a.second > b.second; 
} 
*/
static void
ClientExit(void)
{
   dr_fprintf(gTraceFile,"=====================Heap overflow====================\n\n");
   context_handle_t malloc_ctx,redzone_ctx;
   std::set<int64_t>::iterator it;
   for(it=ctx_red_malloc.begin();it!=ctx_red_malloc.end();it++)
   {
       redzone_ctx=(context_handle_t)((int64_t)(*it)>>32);
       malloc_ctx=(context_handle_t)(((int64_t)(*it)<<32)>>32);
       dr_fprintf(gTraceFile, "------------------- full call path of Malloc allocations is below: context:%ld\n ",malloc_ctx);
       dr_fprintf(gTraceFile,"===================================================\n");
       drcctlib_print_ctxt_hndl_msg(gTraceFile,
               (context_handle_t)malloc_ctx,
               false, false);
       drcctlib_print_full_cct(gTraceFile, (context_handle_t)malloc_ctx, true, false,
               MAX_CLIENT_CCT_PRINT_DEPTH);

       dr_fprintf(gTraceFile, "------------------full call path of Overflow memory loads and stores is below: conext:%ld\n ",redzone_ctx);
       dr_fprintf(gTraceFile,"===================================================\n");
       drcctlib_print_ctxt_hndl_msg(gTraceFile,
               (context_handle_t)redzone_ctx,
               false, false);
       drcctlib_print_full_cct(gTraceFile, (context_handle_t)redzone_ctx, true, false,
               MAX_CLIENT_CCT_PRINT_DEPTH);

       dr_fprintf(gTraceFile,"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n");
   }
   dr_close_file(gTraceFile);


    drcctlib_exit();

    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_MAI_heap dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_MAI_heap failed to "
                        "unregister in ClientExit");
    }
    dr_mutex_destroy(max_lock);
    drwrap_exit();
    drmgr_exit();
    if (drreg_exit() != DRREG_SUCCESS) {
        DRCCTLIB_PRINTF("failed to exit drreg");
    }
    drutil_exit();
}

static void
wrap_pre(void *wrapcxt, OUT void **user_data)
{
    /* malloc(size) or HeapAlloc(heap, flags, size) */
    size_t sz = (size_t)drwrap_get_arg(wrapcxt, IF_WINDOWS_ELSE(2, 0));
    /* increment the allocation size by 1, as red zone */

    //bool set_arg=drwrap_set_arg(wrapcxt,IF_WINDOWS_ELSE(2, 0),(void *)(sz+(RED_SZ*4)));

    dr_fprintf(gTraceFile,"Testing pre!!!!!!!!!!%d\n\n",sz);
    dr_fprintf(gTraceFile,"Post adding %d\n\n",(size_t)drwrap_get_arg(wrapcxt, IF_WINDOWS_ELSE(2, 0)));
    *user_data = (void *)sz;
}
static void
free_pre(void *wrapcxt, void **user_data)
{
    /* free(addr) or HeapAlloc(heap, flags, size) */
    app_pc B=(app_pc)drwrap_get_arg(wrapcxt,0);
    std::map<app_pc,size_t>::iterator it=MAI.find(B);
    if(it!=MAI.end())
    {
        MAI.erase(B);
        MAI_ctx.erase(B);
    }

}


static void
wrap_post(void *wrapcxt, void *user_data)
{
    size_t sz = (size_t)user_data;
    app_pc B=(app_pc)drwrap_get_retval(wrapcxt); 
    //app_pc R=(B+(int)sz);
    context_handle_t malloc_ctxt_hndl=drcctlib_get_context_handle(
            drwrap_get_drcontext(wrapcxt), 0);
    dr_fprintf(gTraceFile,"Address start= %ld,%d,context= %ld\n\n",B,sz,malloc_ctxt_hndl);
/*    int limit=RED_SZ*4;
    for(int i=0;i<limit;i++)
    {
        redmap.insert({R,malloc_ctxt_hndl});
        R++;
    }
    freemap.insert({B,R});*/
    MAI_ctx.insert({B,malloc_ctxt_hndl});
    MAI.insert({B,sz});


}


static void 
module_load_event(void *drcontext, const module_data_t *mod, bool loaded)
{
    app_pc towrap = (app_pc)dr_get_proc_address(mod->handle, MALLOC_ROUTINE_NAME);
	if (towrap != NULL) {
#ifdef SHOW_RESULTS
        bool ok =
#endif
            drwrap_wrap(towrap, wrap_pre, wrap_post);
#ifdef SHOW_RESULTS
        if (ok) {
            dr_fprintf(STDERR, "<wrapped " MALLOC_ROUTINE_NAME " @" PFX "\n", towrap);
        } else {
            /* We expect this w/ forwarded exports (e.g., on win7 both
             * kernel32!HeapAlloc and kernelbase!HeapAlloc forward to
             * the same routine in ntdll.dll)
             */
            dr_fprintf(STDERR,
                       "<FAILED to wrap " MALLOC_ROUTINE_NAME " @" PFX
                       ": already wrapped?\n",
                       towrap);
        }
#endif
    }
    app_pc freewrap = (app_pc)dr_get_proc_address(mod->handle, FREE_ROUTINE_NAME);

	if (freewrap != NULL) {
#ifdef SHOW_RESULTS
        bool ok =
#endif
            drwrap_wrap(freewrap, free_pre, NULL);
#ifdef SHOW_RESULTS
        if (ok) {
            dr_fprintf(STDERR, "<wrapped " FREE_ROUTINE_NAME " @" PFX "\n", freewrap);
        } else {
            /* We expect this w/ forwarded exports (e.g., on win7 both
             * kernel32!HeapAlloc and kernelbase!HeapAlloc forward to
             * the same routine in ntdll.dll)
             */
            dr_fprintf(STDERR,
                       "<FAILED to wrap " FREE_ROUTINE_NAME " @" PFX
                       ": already wrapped?\n",
                       freewrap);
        }
#endif
    }


}

#ifdef __cplusplus
extern "C" {
#endif

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Client 'drcctlib_MAI_heap'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_MAI_heap "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_MAI_heap "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_MAI_heap "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_MAI_heap "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_MAI_heap dr_raw_tls_calloc fail");
    }
    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    drwrap_init();
    dr_register_exit_event(ClientExit);
    drmgr_register_module_load_event(module_load_event);

    dr_fprintf(gTraceFile,"Testing main!!!!!!!!!!\n\n");
    max_lock = dr_mutex_create();

}

#ifdef __cplusplus
}
#endif
