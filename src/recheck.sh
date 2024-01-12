for i in {80..99}
do 
j = $i - 1 
cp "exp-4$j/solnew" "exp-4$i/solold"
cp "exp-4$i/solold" "exp-4$i/solnew" 
done
