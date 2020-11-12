#include <iostream>
using namespace std;

static int *b=(int *)malloc(sizeof(int)*5);
static int abc=0;
void t1_sub()
{
    abc++;
    return;
}

void t2_sub()
{
    abc--;
    return;
}
void test_1()
{
    b[0]=5;
    for(int i =0;i<100;i++)
    {
        if(b[0]==5)
        {
            t1_sub();
            b[0]=4;
        }
        else
        {
            t2_sub();
            b[0]=5;
        }
    }
    printf("hello %d\n",b[0]);
    return;
}


int main(){
    test_1();
	return 0;
}
