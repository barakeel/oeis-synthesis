if [ -f "config" ]
then
echo 'Keep config'
else
   echo 'Create config from config_template'; 
   cp config_template config 
fi

echo 'Overwrite dir.sml'
sed "s#directory_template#$PWD#g" dir_template > dir.sml

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
  echo "Could not find a MKL directory."
fi
