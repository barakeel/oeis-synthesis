if [ -z "$1" ]; then
  echo "Error: Argument is empty."
  exit 1
fi

export OMP_NUM_THREADS=1
export MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
EXP=$1
sed "s#expname_template#$EXP#g" search_script_template > search_script
sed "s#expname_template#$EXP#g" train_script_template > train_script
../HOL/bin/hol --maxheap=50000 < search_script > search_script.out & \
../HOL/bin/hol --maxheap=50000 < train_script > train_script.out
