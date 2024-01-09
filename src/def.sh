EXP=$1
sed "s#expname_template#$EXP#g" def_script_template > def_script
../HOL/bin/hol --maxheap=50000 < def_script > def_script.out
