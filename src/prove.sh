EXP=$1
sed "s#expname_template#$EXP#g" prove_script_template > prove_script
../HOL/bin/hol --maxheap=50000 < prove_script > prove_script.out
