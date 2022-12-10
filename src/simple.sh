EXP=$1
sed "s#expname_template#$EXP#g" simple_script_template > simple_script
../HOL/bin/hol < simple_script > simple_script.out
