DIR=$PWD

## PolyML: installation
cd $DIR
echo "Installing Poly/ML 5.9"
git clone https://github.com/polyml/polyml
cd polyml
git checkout fixes-5.9
./configure --prefix=$PWD
make
make install
export LD_LIBRARY_PATH=$PWD/lib:$LD_LIBRARY_PATH

## PolyML: safety check 
if [ -f "lib/libpolyml.so" ] && [ -f "bin/poly" ]
then
echo 'Installing Poly/ML: success'
else
   echo 'Installing Poly/ML: failure, aborting'; 
   exit 1
fi

## HOL: installation
cd $DIR
echo "Installing HOL (commit cf03ce2dc)"
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
git checkout cf03ce2dc756feb6c0bc4b042f879595d21f2e68
$DIR/polyml/bin/poly < "tools/smart-configure.sml"
cat tools/sequences/kernel tools/sequences/core-theories > shortseq
bin/build --seq=shortseq

## HOL: safety check 
if [ -f "bin/hol" ] && [ -f "bin/Holmake" ]
then
echo 'Installing HOL: success'
else
   echo 'Installing HOL: failure, aborting'; 
   exit 1
fi

## OpenBLAS: installation
cd $DIR
echo "Installing OpenBLAS (version 0.3.21)"
git clone https://github.com/xianyi/OpenBLAS
cd OpenBLAS
git checkout b89fb708caa5a5a32de8f4306c4ff132e0228e9a
make

if [ -f "libopenblas.a" ]
then
echo 'Installing OpenBLAS: success'
else
   echo 'Installing HOL: failure, aborting'; 
   exit 1
fi

cd $DIR
