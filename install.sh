
if [ -f "config" ]
then
echo 'Keep config'
else
   echo 'Create config from config_template'; 
   cp config_template config 
fi

sed "s#directory_template#$PWD#g" dir_template > dir.sml
DIM=$(grep '^dim_glob' config_template | sed -e 's/dim_glob *//')

echo 'Overwrite tree.c with tree_template and config parameters'
sed "s#directory_template#$PWD/tnn_in_c#g" tnn_in_c/tree_template > tnn_in_c/tree_temp
sed "s#dimension_template#$DIM#g" tnn_in_c/tree_temp > tnn_in_c/tree.c
rm tnn_in_c/tree_temp

echo 'Overwrite tnn_in_c/ob_fst.c with tnn_in_c/ob_fst_template and config parameters'
sed "s#dimension_template#$DIM#g" tnn_in_c/ob_fst_template > tnn_in_c/ob_fst.c

if [ -f "tnn_in_c/compile_ob.sh" ]
then
echo 'Keep tnn_in_c/compile_ob.sh'
else
   echo 'Create tnn_in_c/compile_ob.sh from tnn_in_c/compile_ob_thibault.sh'; 
   cp tnn_in_c/compile_ob_thibault.sh tnn_in_c/compile_ob.sh
fi

Holmake cleanAll
Holmake

echo "Installation completed: training additionally requires manually compiling the tnn_in_c/tree.c file"
