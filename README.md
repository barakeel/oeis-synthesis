This repository contains the software OmegaSynt accompanying the paper "Program Synthesis for the OEIS".

Solutions found during a training run can be inspected in the file
`result/full_prog`.

### Try the Web interface
http://grid01.ciirc.cvut.cz/~thibault/synt.html
The web interface has a limited timeout and a limited number of predictions. 

### Install a modified HOL (required)
In your /home/your_username directory:

```
sudo apt install rlwrap
sudo apt install polyml
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
git checkout 0782c4413311d5debebda3f2e6cac9560911cb64
poly < "tools/smart-configure.sml"
cat tools/sequences/kernel tools/sequences/core-theories > shortseq
bin/build --seq=shortseq
```

Edit your .bashrc (or .bash_aliases) by adding the following line:
PATH=/home/your_username/HOL/bin:$PATH

### Install oeis-synthesis:
In this directory, edit the file kernel.sml by replacing the value of
`val selfdir = "/home/thibault/oeis-synthesis"` by 
`val selfdir = "the_directory_where_this_file_is_located"`.

Save the file and run in this directory:
```
Holmake
```

### Test oeis-synthesis (requires 10GB of ram to run with a timeout of 600.0 seconds):
In this directory:
```
rlwrap hol
load "synt"; open synt;
val _ = synt 60.0 [1,2,4,8,16]; 
val _ = synt 30.0 [2,4,8,16,32]; 

val po = synt 20.0 [1,2,3,4];
seq 10 (valOf po);
```

Choose the sequence you desire to look for instead of
[1,2,4,8,16] and you may set the timeout to another value than 60.0 seconds.
Compared to the paper, compr(\\(x.i).p,a,b) is written compr(\\x.p,a,b)
as p should never depend on i.

You can set the following flag to prevent polynomial normalization of the program:
```
kernel.polynorm_flag := false;
```

### Train oeis-syntheis (requires 200GB of ram and 20 cores):
In this directory:
```
rlwrap hol
load "mcts"; open mcts;
expname := "your_experiment_name";
time_opt := SOME 600.0;
(* use_mkl := true; if you have installed mkl *)
rl_search "" 0;
```

### Install MKL libary (optional for faster training)
Downloading/Installing MKL:
```
Ubuntu 20.04: sudo apt install intel-mkl
Ubuntu 18.04: https://github.com/eddelbuettel/mkl4deb 
```
Initializing bash variables:
```
  export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
  export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
  sh /opt/intel/mkl/bin/mklvars.sh intel64
```

In the tnn_in_c directory and run: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```
