ancestor() {
  local n=${1:-1}
  (for ((; n != 0; n--)); do cd $(dirname ${PWD}); done; pwd)
}
OBDIR=$(ancestor 2)/OpenBLAS
OBFILE=$OBDIR/libopenblas.a
if [ -f $OBFILE ]
then
  export LD_LIBRARY_PATH=$OBDIR:$LD_LIBRARY_PATH
  export OPENBLAS_NUM_THREADS=1
  rm ob.o
  rm ob.so
  gcc -fPIC -c ob.c -o ob.o -I$OBDIR
  gcc -shared -o ob.so ob.o /usr/lib/x86_64-linux-gnu/libm.a $OBFILE
else
  echo "$OBFILE does not exists: if you installed OpenBLAS 
        in a different directory consider creating a symlink.
        If you do not want to use OpenBLAS run tnn.use_ob := false;
        in you interactive shell"
fi
