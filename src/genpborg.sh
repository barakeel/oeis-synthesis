EXP=$1
sed "s#expname_template#$EXP#g" genpborg_script_template > genpborg_script
../HOL/bin/hol --maxheap=50000 < genpborg_script > genpborg_script.out
