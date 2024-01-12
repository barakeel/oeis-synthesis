for i in $(seq 80 99)
do 
j=$((i-1)) 
cp "exp/exp4$j-chk/solnew" "exp/exp4$i-chk/solold"
sh check.sh "exp4$i-chk"
done
