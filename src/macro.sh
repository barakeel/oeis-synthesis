EXP=$1
sed "s#expname_template#$EXP#g" macro_script_template > macro_script
../HOL/bin/hol < macro_script > macro_script.out
