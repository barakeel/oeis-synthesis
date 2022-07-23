gcc -o tree tree.c -DMKL_ILP64 -m64 -I/usr/include/mkl -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
