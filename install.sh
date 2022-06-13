
if [ -f "config" ]
then
echo 'Proceeding with parameters from "config"'
else
   echo 'File "config" not found: copying it from "config_template"'; 
   cp config_template config 
fi

sed "s#directory_template#$PWD#g" dir_template > dir.sml
sed "s#directory_template#$PWD#g" tnn_in_c/tree_template > tnn_in_c/tree.c
Holmake cleanAll
Holmake

echo "Installation completed: training will additionally require manually compiling the tnn_in_c/tree.c file"
