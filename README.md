This repository contains the software QSynt accompanying the paper 
"Learning Program Synthesis for Integer Sequences from Scratch". 

Solutions found during the full-scale self-learning run 
can be inspected in the file `results/solutions`.

The following installation instructions are for the Ubuntu OS.

### Web interface
Try QSynt before installing it at http://grid01.ciirc.cvut.cz/~thibault/qsynt.html.

### Install dependencies: MKL,polyml,HOL,OpenBLAS (takes about 20min)
```
sudo apt install rlwrap intel-mkl
sh install_dep.sh
```

### Install oeis-synthesis
```
cd src
wget http://grid01.ciirc.cvut.cz/~thibault/model.tar.gz
tar -xvf model.tar.gz
sh install.sh
```

After updating the repository (git pull), 
the command `sh install.sh` needs to be run again.


### Test oeis-synthesis (requires 10GB of ram to run with a timeout of 600.0 seconds)
In `src`, run `sh hol.sh` then run in the interative shell:
```
load "qsynt"; open qsynt;

(* make search times out after 10 seconds *)
game.time_opt := SOME 10.0;
(* launch the search *)
val p = valOf (qsynt "2 4 16 256");
(* result in native programming language *)
aiLib.print_endline (human.humanf p);
(* result in Python *)
aiLib.print_endline (human.human_python 10 p);
(* first n generated terms *)
val seq = exec.penum p 10;

(* an example where the search fails *)
val po = qsynt "2 5 16 256";
```

### Train oeis-syntheis (requires 4GB of ram per core)
To change training options, edit the `src/config` file and 
run `sh install.sh` again.
In `src`, run `sh hol.sh` then run in the interative shell:
```
load "rl"; open rl;
expname := "your_experiment";
rl_search 0;
```

### Known issues:

####How do I install MKL for older versions of Ubuntu?
See https://github.com/eddelbuettel/mkl4deb

After installing, you need to add the following lines to your `/home/user/.bash_aliases`:
```
export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
sh /opt/intel/mkl/bin/mklvars.sh intel64
```

#### Problem when compiling FFI (sh compile_ob.sh)
Please install in the `oeis-synthesis` directory: 
```
git clone https://github.com/JuliaMath/openlibm
cd openlibm
make
```





