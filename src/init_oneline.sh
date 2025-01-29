EXP=$1
sed "s#expname_template#$EXP#g" init_oneline_script_template > init_oneline_script
../HOL/bin/hol --maxheap=50000 < init_oneline_script > init_oneline_script.out
