EXP=$1
FILE=$2
cat genpborg_script_template | sed "s#expname_template#$EXP#g"  | sed "s#file_template#$FILE#g" > genpborg_script

../HOL/bin/hol --maxheap=50000 < genpborg_script > genpborg_script.out
