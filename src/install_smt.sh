if [ -f "config" ]
then
echo 'Keep config'
else
   echo 'Create config from config_template_smt'; 
   cp config_template_smt config 
fi

echo 'Overwrite dir.sml'
sed "s#directory_template#$PWD#g" dir_template > dir.sml

echo "Creating Standard ML dependency files"
../HOL/bin/Holmake --nolmbc cleanAll
../HOL/bin/Holmake --nolmbc
