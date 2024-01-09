EXP=$1
sed "s#expname_template#$EXP#g" check_script_template > check_script
../HOL/bin/hol --maxheap=50000 < check_script > check_script.out
