
if [ -f "config" ]
then
echo 'Keep config'
else
   echo 'Create config from config_template'; 
   cp config_template config 
fi

sed "s#directory_template#$PWD#g" dir_template > dir.sml
DIM=$(grep '^dim_glob' config_template | sed -e 's/dim_glob *//')

echo 'Overwrite tree.c'
sed "s#directory_template#$PWD/tnn_in_c#g" tnn_in_c/tree_template > tnn_in_c/tree_temp
sed "s#dimension_template#$DIM#g" tnn_in_c/tree_temp > tnn_in_c/tree.c
rm tnn_in_c/tree_temp

echo 'Overwrite tnn_in_c/ob_fst.c'
sed "s#dimension_template#$DIM#g" tnn_in_c/ob_fst_template > tnn_in_c/ob_fst.c

Holmake cleanAll
Holmake

. /etc/lsb-release

cd tnn_in_c

if [ "$DISTRIB_RELEASE" = "18.04" ]; then
  echo "Compiling MKL tree.c for Ubuntu 18.04"
  sh compile_mkl18.sh
elif [ "$DISTRIB_RELEASE" = "20.04" ]; then
  echo "Compiling MKL tree.c for Ubuntu 20.04"
  sh compile_mkl20.sh
else
  echo "Compiling MKL tree.c for Ubuntu $DISTRIB_RELEASE: defaulting to Ubuntu 20.04"
  sh compile_mkl20.sh
fi
