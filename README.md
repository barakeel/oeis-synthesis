This repository contains the software QSynt accompanying the paper 
"Learning Program Synthesis for Integer Sequences from Scratch". 


Solutions found during the full-scale self-learning run can be inspected in the file `results/solutions`.

### Try the Web interface
http://3.71.110.215/~anon/qsynt.html

### Install on the Ubuntu OS a modified HOL (required)
In your /home/your_username directory:

```
sudo apt install rlwrap
sudo apt install polyml
sudo apt install libpolyml-dev
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
git checkout cf03ce2dc756feb6c0bc4b042f879595d21f2e68
poly < "tools/smart-configure.sml"
cat tools/sequences/kernel tools/sequences/core-theories > shortseq
bin/build --seq=shortseq
```

Edit your .bashrc (or .bash_aliases) by adding the following line:
PATH=/home/your_username/HOL/bin:$PATH

### Install oeis-synthesis:
In this directory, edit the file `dir.sml` by replacing the value of
`val selfdir = "/home/user/oeis-synthesis"` by 
`val selfdir = "the_directory_where_this_file_is_located"`.

Save the file and run in this directory:
```
Holmake
```

### Test oeis-synthesis (requires 10GB of ram to run with a timeout of 600.0 seconds):
In this directory run `rlwrap hol` then run in the interative shell:

```
load "qsynt"; open aiLib human rl qsynt;
time_opt := SOME 60.0;
polynorm_flag := true; (* optional *)

val po = qsynt (map Arbint.fromInt [3,5,7]);
val p = valOf po;
print_endline (humanf p);
val seq = penum p 8;

val po = qsynt (map Arbint.fromInt [2,4,16,256]);
val p = valOf po;
print_endline (humanf p);
val seq = penum p 10;
```

### Train oeis-syntheis (requires 200GB of ram and 20 cores):
In this directory run `rlwrap hol` then run in the interative shell:
```
load "rl"; open rl;
expname := "your_experiment";
rl_search "_main" 1;
```

### Install MKL libary (optional for faster training)
#### Ubuntu 20.04
```
sudo apt install intel-mkl
```

Edit the `tnn_in_c/tree.c` file: 

Change `/home/user/oeis-synthesis/tnn_in_c/`
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

Change `/home/user/oeis-synthesis/tnn_in_c/`
to the absolute path to your  `tnn_in_c` directory.


In the `tnn_in_c` directory and compile `tree.c`: 
```
  gcc -o tree tree.c -DMKL_ILP64 -m64 -I/opt/intel/mkl/include -L/opt/intel/lib/intel64 -L/opt/intel/mkl/lib/intel64 -Wl,--no-as-needed -lmkl_intel_ilp64 -lmkl_intel_thread -lmkl_core -liomp5 -lpthread -lm -ldl
```
