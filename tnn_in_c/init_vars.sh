#copy paste those to your bash (executing this won't work)

export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
sh /opt/intel/mkl/bin/mklvars.sh intel64
export OPENBLAS_NUM_THREADS=2
export LD_LIBRARY_PATH=/home/thibault/big/OpenBLAS:$LD_LIBRARY_PATH
