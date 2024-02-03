DIR=$PWD
mkdir exp/nmt$1
cd exp/nmt$1
scp 10.35.125.70:/home/mptp/big3/oe3-run1-op1/big-merge/out1/00.z$1.gz z$1.gz
gunzip z$1.gz
echo "adding spaces"
awk -F':' '{gsub(/./, "& ", $3); print $3}' z$1 > cand
echo "()" > solold
cd $DIR
echo "start checking"
sh check.sh nmt$1
echo "end checking"
cd exp/nmt$1
if [ -f "solnew" ]; then
  rm z$1.gz z$1 cand
  rm -r split
else
  echo "failure"
  exit 1
fi
cd $DIR
