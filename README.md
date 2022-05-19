This repository contains the software QSynt accompanying the paper "Program Synthesis for the OEIS". The preprint is available [here](https://arxiv.org/abs/2202.11908).

Solutions found during a training run can be inspected in the file
`result/full_prog`.

### Try the Web interface
http://grid01.ciirc.cvut.cz/~thibault/qsynt.html

### Install on the Ubuntu OS a modified HOL (required)
In your /home/your_username directory:

```
sudo apt install rlwrap
sudo apt install polyml
sudo apt install libpolyml-dev
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
In this directory, edit the file `dir.sml` by replacing the value of
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
val _ = synt 60.0 16 [1,2,4,8,16]; 
val _ = synt 30.0 16 [2,4,8,16,32]; 
val _ = synt 20.0 16 [1,2,3,4];
```

Choose the sequence you desire to look for instead of
[1,2,4,8,16] and you may set the timeout to another value than 60.0 seconds.
The second argument (16) precises the number of generated numbers (predictions).

You can set the following flag to apply polynomial normalization to the program:
```
kernel.polynorm_flag := true;
```

### Train oeis-syntheis (requires 200GB of ram and 20 cores):
In this directory:
```
rlwrap hol
load "mcts"; open mcts;
expname := "your_experiment_name";
time_opt := SOME 600.0;
(* use_mkl := true; if you have installed mkl *)
bloom.init_od ();
rl_search "" 0;
```

### Install MKL libary (optional for faster training)
#### Ubuntu 20.04
```
sudo apt install intel-mkl
```

Edit the `tnn_in_c/tree.c` file: 

Change `/home/thibault/big/repos/oeis/tnn_in_c/`
to the absolute path to your  `tnn_in_c` directory.

In the `tnn_in_c` directory and compile `tree.c`: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/usr/include/mkl -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```

#### Ubuntu 18.04

See https://github.com/eddelbuettel/mkl4deb 

Initializing bash variables:
```
  export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
  export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
  sh /opt/intel/mkl/bin/mklvars.sh intel64
```

Edit the `tnn_in_c/tree.c` file: 

Change `/home/thibault/big/repos/oeis/tnn_in_c/`
to the absolute path to your  `tnn_in_c` directory.


In the `tnn_in_c` directory and compile `tree.c`: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```
