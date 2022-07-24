This repository contains the software QSynt accompanying the paper 
"Learning Program Synthesis for Integer Sequences from Scratch". 

Solutions found during the full-scale self-learning run 
can be inspected in the file `results/solutions`.

The following installation instructions are for the Ubuntu OS.

### Try the Web interface
http://grid01.ciirc.cvut.cz/~thibault/qsynt.html

### Install dependencies: MKL,polyml,HOL,OpenBLAS (takes about 20min)
```
sudo apt install rlwrap
sudo apt install intel-mkl
sh install_dep.sh
```

If your version of Ubuntu is less than 20.04 follow the steps in the last paragraph for installing `intel-mkl`.

### Install oeis-synthesis
```
cd src
sh install.sh
```

### Test oeis-synthesis (requires 10GB of ram to run with a timeout of 600.0 seconds)
In `src`, run `sh hol.sh` then run in the interative shell:
```
load "qsynt"; open aiLib human exec rl qsynt;
game.time_opt := SOME 60.0;
val po = qsynt (map Arbint.fromInt [2,4,16,256]);
val p = valOf po;
print_endline (humanf p);
val seq = penum p 10;
```

### Train oeis-syntheis (requires 200GB of ram and 20 cores)
To change training options, edit the `src/config` file and 
run `sh install.sh` again.
In `src`, run `sh hol.sh` then run in the interative shell:
```
load "rl"; open rl;
expname := "your_experiment";
rl_search 0;
```


### How do I install MKL for older versions of Ubuntu?
See https://github.com/eddelbuettel/mkl4deb

After installing, you need to add the following lines to your `/home/user/.bash_aliases`:
```
export LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:$LD_LIBRARY_PATH
export LD_LIBRARY_PATH=/opt/intel/lib/intel64:$LD_LIBRARY_PATH
sh /opt/intel/mkl/bin/mklvars.sh intel64
```







