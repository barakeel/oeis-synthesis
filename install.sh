sed "s#directory_template#$PWD#g" dir_template > dir.sml
sed "s#directory_template#$PWD#g" tnn_in_c/tree_template > tnn_in_c/tree.c
Holmake cleanAll
Holmake
