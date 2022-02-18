## Install a modified HOL (required)
```
sudo apt install rlwrap
sudo apt install polyml
git clone https://hol-theorem-prover.org/HOL
cd HOL
git checkout 3ff450a0a80a45ab2336801759b9dc3426cfe8c5
poly < "tools/smart-configure.sml"
bin/build
```

Edit your .bashrc (or .bash_aliases) by adding the following line:
PATH=~/HOL/bin:$PATH

#### Install oeis-synthesis:
In this directory:

Edit the file kernel.sml and change the line
`val selfdir = "/home/thibault/oeis-synthesis";`
to `val seldir = "your_oeis-synthesis_directory";`

Then run the commands:
```
Holmake cleanAll
Holmake
```
#### Test oeis-synthesis:
In this directory:
```
rlwrap hol
load "mcts"; open mcts;
search_target 60.0 [1,2,4,8,16]; 
```

Choose the sequence you desire to look for instead of
[1,2,4,8,16] and you may set the timeout to another value than 60.0 seconds.


#### Train oeis-syntheis (requires 200GB of ram and 20 cores):
In this directory:
```
rlwrap hol
load "mcts"; open mcts;
expname := "your_experiment_name";
time_opt := SOME 600.0;
(* use_mkl := true; if you have installed mkl *)
rl_search "" 0;
```

#### Install MKL libary (optional for faster training)
Downloading/Installing MKL:
```
Ubuntu 20.04: sudo apt install intel-mkl
Ubuntu 18.04: https://github.com/eddelbuettel/mkl4deb 
```
Initializing bash variables:
  export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
  export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
  sh /opt/intel/mkl/bin/mklvars.sh intel64

Compiling in tnn_in_c directory: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```

#### Known bugs: 
  Multiple threads might be creating the same experiment directory during 
training.
  Restarting will fix the problem since the directory was created.

