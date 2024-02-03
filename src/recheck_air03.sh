mkdir exp/nmt$1
cd exp/nmt$1
scp 10.35.125.70:/home/mptp/big3/oe3-run1-op1/big-merge/out1/00.z$1.gz z$1.gz
gunzip -o candorg z$1.gz
awk -F':' '{print $3}' candorg | sed 's/\(.\)/\1 /g; s/ $//' > cand
cd ../..
sh check.sh nmt$1
cd exp/nmt$1
rm z$1.gz candorg cand
rm -r split
cd ../..
