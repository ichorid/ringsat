#!/bin/bash
#nvcc -Xptxas   -O5  -arch=sm_21 --ptxas-options="-v -dlcm=cg"  -I ./ -o ./solver_cuda.o -c ./solver_cuda.cu
nvcc -lineinfo -lcuda  -O5 -arch=sm_21    --ptxas-options="-v -dlcm=cg"  -I ./ -o ./solver_cuda.o -c ./solver_cuda.cu
g++ -O5   -o ./ringsat-gpu20 ./solver_cuda.o ./main.cpp -L/usr/local/cuda/lib64 -lcuda -lcudart -I ./ 
