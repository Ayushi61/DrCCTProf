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
#define DRCCTLIB_PRINTF(format, args...) \
    DRCCTLIB_PRINTF_TEMPLATE("drcctlib_memory_footprint", format, ##args)
#define DRCCTLIB_EXIT_PROCESS(format, args...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("drcctlib_memory_footprint.cpp", format, \
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

typedef struct _mem_ref_t {
    app_pc addr;
    size_t size;
} mem_ref_t;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
} per_thread_t;

std::map<context_handle_t, std::set<app_pc>> uniq_bytes;
std::map<char*,std::set<app_pc>> mem_footprint;
#define TLS_MEM_REF_BUFF_SIZE 100

// client want to do
void
DoWhatClientWantTodo(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref)
{
    // add online analysis here
    size_t instr_size=ref->size;
    std::set<app_pc> addr_list;
    app_pc init_add=ref->addr;
    for(int i=0;i<(int)instr_size;i++)
    {
        addr_list.insert(init_add+i);
    }
    if(uniq_bytes.find(cur_ctxt_hndl)==uniq_bytes.end())
        uniq_bytes.insert({cur_ctxt_hndl,addr_list});
    else
        uniq_bytes[cur_ctxt_hndl].insert(addr_list.begin(),addr_list.end());
}
// dr clean call
void
InsertCleancall(int32_t slot,int32_t num)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            DoWhatClientWantTodo(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
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
    char name[MAXIMUM_PATH] = "arm.drcctlib_memory_footprint.out.";
#else
    char name[MAXIMUM_PATH] = "x86.drcctlib_memory_footprint.out.";
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
}

static void
ClientExit(void)
{
    // add output module here
    std::map<context_handle_t,std::set<app_pc>>::iterator it;
	std::map<char*,std::set<app_pc>>::iterator it_map;
	char *func_name;
	std::set<app_pc> temp_set;
    int i=0,i1=0;
    for(it=uniq_bytes.begin();it!=uniq_bytes.end();it++)
    {

     context_t *ctxt=drcctlib_get_full_cct(it->first,0);
     context_handle_t loop_hndl=it->first;
     while(loop_hndl!=THREAD_ROOT_SHARDED_CALLER_CONTEXT_HANDLE)
     {
        ctxt=ctxt->pre_ctxt;
        loop_hndl=ctxt->ctxt_hndl;
		func_name=ctxt->func_name;
        if(uniq_bytes.find(loop_hndl)!=uniq_bytes.end())
        {
            uniq_bytes.find(loop_hndl)->second.insert(it->second.begin()
                ,it->second.end());
			temp_set.insert(it->second.begin(),it->second.end());
			it_map=mem_footprint.find(func_name);
			if(it_map==mem_footprint.end())
			{
				mem_footprint.insert({func_name,temp_set});
			}
			else
				mem_footprint[func_name]=temp_set;

            i1++;
			
        }
     }
    }
    //dr_fprintf(gTraceFile, "i1= %d ----------------------\n",
    //                                                i1);
//    std::set<app_pc>::iterator itr;
  /*  for(it=uniq_bytes.begin();it!=uniq_bytes.end();it++)
    {

     dr_fprintf(gTraceFile, "No. %d memory footprint is %d ctxt handle %lld====",
                                        i,it->second.size(),it->first);

     drcctlib_print_ctxt_hndl_msg(gTraceFile, it->first, false, false);
     dr_fprintf(gTraceFile,
        "====================================================================="
        "===========\n");
//     for(itr=it->second.begin();itr!=it->second.end();itr++)
     {
           dr_fprintf(gTraceFile, "%X,",*itr,false,false);
     }
//    dr_fprintf(gTraceFile,"****\n");

    drcctlib_print_full_cct(gTraceFile, it->first, true, false,
                                MAX_CLIENT_CCT_PRINT_DEPTH);
    dr_fprintf(gTraceFile,
                   "====================================================================="
                   "===========\n\n\n");
     i++;
    }
*/
	std::map<char*,std::set<app_pc>>::iterator it1;
    for(it1=mem_footprint.begin();it1!=mem_footprint.end();it1++)
    {

     dr_fprintf(gTraceFile, "No. %d memory footprint is %d ctxt handle ====%s",
                                        i,it->second.size(),it1->first);

     //drcctlib_print_ctxt_hndl_msg(gTraceFile, it->first, false, false);
     dr_fprintf(gTraceFile,
        "====================================================================="
        "===========\n");
   /*  for(itr=it->second.begin();itr!=it->second.end();itr++)
     {
           dr_fprintf(gTraceFile, "%X,",*itr,false,false);
     }
    dr_fprintf(gTraceFile,"****\n");*/

//    drcctlib_print_full_cct(gTraceFile, it->first, true, false,
  //                              MAX_CLIENT_CCT_PRINT_DEPTH);
    dr_fprintf(gTraceFile,
                   "====================================================================="
                   "===========\n\n\n");
     i++;
    }
    drcctlib_exit();

    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_memory_footprint dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_memory_footprint failed to "
                        "unregister in ClientExit");
    }
    drmgr_exit();
    if (drreg_exit() != DRREG_SUCCESS) {
        DRCCTLIB_PRINTF("failed to exit drreg");
    }
    drutil_exit();
}

#ifdef __cplusplus
extern "C" {
#endif

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Client 'drcctlib_memory_footprint'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_footprint "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_footprint "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_footprint "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_footprint "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_memory_footprint dr_raw_tls_calloc fail");
    }
    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif
