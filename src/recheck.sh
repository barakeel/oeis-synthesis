for i in {80..99}
do 
j=$((i-1)) 
cp "exp4$j-chk/solnew" "exp4$i-chk/solold"
cp "exp4$i-chk/solold" "exp4$i-chk/solnew" 
done
