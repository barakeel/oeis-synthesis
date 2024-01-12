for i in {80..99}
do 
j=$((i-1)) 
cp "exp/exp4$j-chk/solnew" "exp/exp4$i-chk/solold"
cp "exp/exp4$i-chk/solold" "exp/exp4$i-chk/solnew" 
done
