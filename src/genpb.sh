EXP=$1
sed "s#expname_template#$EXP#g" genpb_script_template > genpb_script
../HOL/bin/hol --maxheap=50000 < genpb_script > genpb_script.out
