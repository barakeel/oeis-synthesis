EXP=$1
sed "s#expname_template#$EXP#g" macro_script_template > macro_script
../HOL/bin/hol --maxheap=50000 < macro_script > macro_script.out
