EXP=$1
sed "s#expname_template#$EXP#g" dedupl_script_template > dedupl_script
../HOL/bin/hol --maxheap=50000 < dedupl_script > dedupl_script.out
