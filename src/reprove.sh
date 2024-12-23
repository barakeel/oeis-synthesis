EXP=$1
sed "s#expname_template#$EXP#g" reprove_script_template > reprove_script
../HOL/bin/hol --maxheap=50000 < reprove_script > reprove_script.out
