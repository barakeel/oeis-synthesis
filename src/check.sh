sed "s#expname_template#$EXP#g" check_script_template > check_script
../HOL/bin/hol < check_script > check_script.out
