
if [ -f "config" ]
then
echo 'Proceeding with parameters from "config"'
else
   echo 'File "config" not found: copying it from "config_template"'; 
   cp config_template config 
fi

sed "s#directory_template#$PWD#g" dir_template > dir.sml
DIM=$(grep '^dim_glob' config_template | sed -e 's/dim_glob *//')
sed "s#directory_template#$PWD#g" tnn_in_c/tree_template > tnn_in_c/tree_temp
sed "s#dimension_template#$DIM#g" tnn_in_c/tree_temp > tnn_in_c/tree.c
rm tnn_in_c/tree_temp

Holmake cleanAll
Holmake

echo "Installation completed: training additionally requires manually compiling the tnn_in_c/tree.c file"
