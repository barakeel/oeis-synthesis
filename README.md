## Install a modified HOL (required)

Install HOL:
```
sudo apt install polyml
git clone https://hol-theorem-prover.org/HOL
cd HOL
git checkout 3ff450a0a80a45ab2336801759b9dc3426cfe8c5
poly < "tools/smart-configure.sml"
```

Edit your .bashrc (or .bash_aliases) by adding the following line:
PATH=~/HOL/bin:$PATH


## Install OEIS-synthesis:
Change directory value of selfdir in kernel.sml 
to the directory where this README is located.
Run Holmake in the directory in which this file is located.

## Test OEIS-synthesis:
  









## Train OEIS-syntheis: 
  (only do this if you have 200GB of ram and 20 cores or 
   figure how to change these parameters in mcts.sml)






## Install MKL libary (optional for faster training)
Downloading mkl:
  Ubuntu 20.04: sudo apt install intel-mkl
  Ubuntu 18.04: https://github.com/eddelbuettel/mkl4deb 

Initializing bash variables:
  export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
  export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
  sh /opt/intel/mkl/bin/mklvars.sh intel64

Compiling in tnn_in_c directory: 
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl

use_mkl := true;
rl_search "your_choice" 0; 


## Known bugs: 
  Multiple threads might be creating the same directory when starting training. 
  just need to 
  if the training is stalling a restart will fix it since the directory will be created.

