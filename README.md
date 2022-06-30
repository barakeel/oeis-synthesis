This repository contains the software QSynt accompanying the paper 
"Learning Program Synthesis for Integer Sequences from Scratch". 

Solutions found during the full-scale self-learning run 
can be inspected in the file `results/solutions`.

### Try the Web interface
http://grid01.ciirc.cvut.cz/~thibault/qsynt.html

### Installations remarks
The software installed (polyml,HOL,oeis-synthesis,OpenBLAS) except the mkl
are assumed to be installed locally in the same directory.
In the following, we will assume that this directory is /home/user.
This file should be in the /home/user/oeis-synthesis directory.
If not, some of the following instructions need to be adapted accordingly.

### Install polyml version 5.9 or higher from source
In your /home/user directory:
```
git clone https://github.com/polyml/polyml
cd polyml
git checkout fixes-5.9
./configure --prefix=/usr
make
make install
```

### Install HOL (a modified version)
In your /home/user directory:
```
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
git checkout cf03ce2dc756feb6c0bc4b042f879595d21f2e68
poly < "tools/smart-configure.sml"
cat tools/sequences/kernel tools/sequences/core-theories > shortseq
bin/build --seq=shortseq
```

Add to your .bashr the following line:
```
PATH=/home/user/HOL/bin:$PATH
```

### Install oeis-synthesis
In the directory where this 

Copy and modify values of the `config` file (optional):
```
cp config_template config
```

Run in this directory:
```
sh install.sh
```

### Test oeis-synthesis (requires 10GB of ram to run with a timeout of 600.0 seconds)
In this directory run `rlwrap hol` (sudo apt install rlwrap) 
then run in the interative shell:

```
load "qsynt"; open aiLib human exec rl qsynt;
tnn.use_ob := false;
game.time_opt := SOME 60.0;
val po = qsynt (map Arbint.fromInt [2,4,16,256]);
val p = valOf po;
print_endline (humanf p);
val seq = penum p 10;
```

### Install MKL (Required for training)

#### Ubuntu 20.04
```
sudo apt install intel-mkl
```

In the `tnn_in_c` directory and compile `tree.c`: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/usr/include/mkl -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```

#### Ubuntu 18.04
See https://github.com/eddelbuettel/mkl4deb

Initializing bash variables (put in your .bashrc)
```
  export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
  export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
  sh /opt/intel/mkl/bin/mklvars.sh intel64
```

In the `tnn_in_c` directory and compile `tree.c`: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```

### Install OpenBLAS (Faster search using foreign function interface)
In a sibling directory of oeis-synthesis (usually 
home/user directory) run:
```
git clone https://github.com/xianyi/OpenBLAS
```
and follow the install instructions.

Add to your `.bashrc`:
```
export OPENBLAS_NUM_THREADS=1
export LD_LIBRARY_PATH=/home/user/OpenBLAS:$LD_LIBRARY_PATH
```
and replace user by your username.


### Train oeis-syntheis (requires 200GB of ram and 20 cores)
In this directory run `rlwrap hol` then run in the interative shell:
```
load "rl"; open rl;
expname := "your_experiment";
rl_search 0;
```







