OBDIR=$(dirname $(dirname $PWD))/OpenBLAS
OBFILE=$OBDIR/libopenblas.a
if [ -f $OBFILE ]
then
  export LD_LIBRARY_PATH=$OBDIR:$LD_LIBRARY_PATH
  export OPENBLAS_NUM_THREADS=1
  rm ob.o
  rm ob.so
  gcc -fPIC -c ob.c -o ob.o -I$OBDIR
  gcc -shared -o ob_temp.so ob.o /usr/lib/x86_64-linux-gnu/libm.a $OBFILE
  mv ob_temp.so ob.so
  rm ob_temp.so
else
  echo "$OBFILE does not exists"
fi
