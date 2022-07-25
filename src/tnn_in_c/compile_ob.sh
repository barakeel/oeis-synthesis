TOPDIR=$(dirname $(dirname $PWD))
OBDIR=$TOPDIR/OpenBLAS
OBFILE=$OBDIR/libopenblas.a
BASE=$(basename $1 .c)
if [ -f $TOPDIR/openlibm/libopenlibm.a ]
then 
  echo "using locally installed libopenlibm"
  LIBM=$TOPDIR/openlibm/libopenlibm.a
else
  LIBM=/usr/lib/x86_64-linux-gnu/libm.a
fi

if [ -f $OBFILE ]
then
  export LD_LIBRARY_PATH=$OBDIR:$LD_LIBRARY_PATH
  export OPENBLAS_NUM_THREADS=1
  gcc -fPIC -O2 -c $1 -o "$BASE".o -I$OBDIR
  gcc -shared -o "$BASE"_temp.so "$BASE".o $LIBM $OBFILE
  mv "$BASE"_temp.so "$BASE".so
else
  echo "$OBFILE does not exists"
fi
