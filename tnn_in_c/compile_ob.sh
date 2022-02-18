export LD_LIBRARY_PATH=/home/thibault/big/OpenBLAS:$LD_LIBRARY_PATH
export OPENBLAS_NUM_THREADS=2
rm ob.o
rm ob.so
cat ob_fst.c ob_arity ob_head ob_mat ob_snd.c > ob.c
gcc -fPIC -c ob.c -o ob.o -I/home/thibault/big/OpenBLAS
gcc -shared -o ob.so ob.o /usr/lib/x86_64-linux-gnu/libm.a /home/thibault/big/OpenBLAS/libopenblas.a
