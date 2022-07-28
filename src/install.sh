if [ -f "config" ]
then
echo 'Keep config'
else
   echo 'Create config from config_template'; 
   cp config_template config 
fi

echo 'Overwrite dir.sml'
sed "s#directory_template#$PWD#g" dir_template > dir.sml
DIM=$(grep '^dim_glob' config | sed -e 's/dim_glob *//')

echo 'Overwrite tree.c'
sed "s#dimension_template#$DIM#g" tnn_in_c/tree_template > tnn_in_c/tree.c
echo 'Overwrite tnn_in_c/ob_fst.c'
sed "s#dimension_template#$DIM#g" tnn_in_c/ob_fst_template > tnn_in_c/ob_fst.c

echo "Creating Standard ML dependency files"
../HOL/bin/Holmake --nolmbc cleanAll
../HOL/bin/Holmake --nolmbc

cd tnn_in_c
if [ -d "/usr/include/mkl" ]; then
  echo "MKL: /usr/include/mkl"
  sh compile_mkl20.sh
  if [ -f "tree" ]; then
  echo "Binary file tree produced by compile_mkl20.sh"
  else
  echo "Failure when compiling tree.c: unknown issue"
  exit 1
  fi 
elif [ -d "/opt/intel/mkl" ]; then
  echo "MKL: /opt/intel/mkl"
  sh compile_mkl18.sh
  if [ -f "tree" ]; then
  echo "Binary file tree produced by compile_mkl18.sh"
  else
    echo "Failure when compiling tree.c: see known issues in README.md"
    exit 1
  fi 
else
  echo "Could not find a MKL directory. Please install MKL."
fi

cd ..
if [ -d $(dirname $PWD)/OpenBLAS ]; then
  echo "OpenBLAS: $(dirname $PWD)/OpenBLAS"
else
  echo "Could not find OpenBLAS. Please install OpenBLAS in $(dirname $PWD)" 
fi
cd tnn_in_c

sh compile_ob.sh ../model/ob_online.c
if [ -f "ob_online.so" ]; then
  echo "ob_online.so produced by compile_ob.sh"
else
  echo "Failure when compiling ob_online.c with 
        tnn_in_c/compile_ob.sh: see known issues in README.md"
  exit 1
fi
