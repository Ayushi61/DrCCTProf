#!/bin/bash

cd ./spec2006
source ./shrc
cd ./benchspec/CPU2006/456.hmmer/build/build_base_reuse.0000/
make

#run command:
time ./hmmer bombesin.hmm swiss41
#time ./hmmer nph3.hmm swiss41

#To change the compiler, add paths or make clean:
#vim ./spec2006/benchspec/CPU2006/456.hmmer/build/build_base_reuse.0000/Makefile.spec 
