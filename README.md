This repository contains the software accompanying the paper "Program Synthesis for the OEIS".

Solutions found during a training run can be inspected in the file
`result/full_prog_poly`.

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
load "mcts"; open mcts;
search_target 60.0 [1,2,4,8,16]; 
```

Choose the sequence you desire to look for instead of
[1,2,4,8,16] and you may set the timeout to another value than 60.0 seconds.

Results are printed with compressed polynomials in x.
For example, 2 * x * x * x + 2 + 2 is printed as 2x3 + 4.

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
