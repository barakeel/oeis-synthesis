This repository contains the software QSynt accompanying the paper 
"Learning Program Synthesis for Integer Sequences from Scratch". 

Solutions found during the full-scale self-learning run 
can be inspected in the file `results/solutions`.

The following installation instructions are for the Ubuntu OS.

### Web interface
Try QSynt before installing it at http://grid01.ciirc.cvut.cz/~thibault/qsynt.html.

### Install dependencies: MKL,polyml,HOL,OpenBLAS (takes about 20min)
``` 
sudo apt install -y libgmp-dev rlwrap intel-mkl
sh install_dep.sh
```

Tip: Installing `intel-mkl` requires 2GB but is not necessary if you only want to run the checker.

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
Go to the `src` directory.
Run `sh hol.sh` then run in the interative shell:
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
Go to the `src` directory and run:
```
sh rl.sh expname
```

- To change training options, 
  edit the `config` file and run `sh install.sh` again.
- You may change `expname` to reflect the aim of your experiment.
- You can stop the training at any point by interrupting the process 
  with ctrl+c. 
- You can restart the training from the last generation
by running the same command `sh rl.sh expname`.

A summary of the number of programs found at different generation is located at
`src/exp/expname/log`.
Resulting programs can be inspected in the directory `src/exp/expname/search/gen/full_prog` where `gen` is a generation number.
Running multiple instances of ``rl.sh`` on the same machine may fail.

### Running the checker
Go to the `src` directory and create the directories `exp` and `exp/expname`.
In `exp/expname`, add two files: `solold` set of previous 
solutions in lisp format,
and `cand` a set of candidate program should be listed in 
reverse reverse polish notation (e.g. prefix notation).
Run in the src directory:

```
sh check.sh expname
```

You may change `expname` to reflect the aim of your experiment.
To change the checking options, edit the `config` file. The relevant entries 
are `ncore`, `search_memory` and `sol2_flag`.

The programs will produce two files `solnew` and `solnewgpt`.
`solnewgpt` can be used to trained your machine learning model an create a new `cand` file. The format is "sequence>program"
The program is written in reverse polish notation. 

Tip: If you do not have any solold file you may create a new solold file with "()" written in the first line.


#### Bootstrapping a external self-learning process
You can start a self-learning process by starting from the files `sol0` (to rename to `solold`) and `sol0gpt` to be used to produce the `cand` file.
These files can be dowloaded by running:

```
wget http://grid01.ciirc.cvut.cz/~thibault/oeis-gpt/sol0
wget http://grid01.ciirc.cvut.cz/~thibault/oeis-gpt/sol0gpt
```

These files were generated using a random generator and selecting the smallest and fastest programs (`sol2_flag true` in the `config` file).
Moving the file `solnew` from a `expname=generation_n` directory to 
the file `solold` of a `expname=generation_n+1` directory is left to the user.

##External machine learner
Disclaimer: the following toolkit is hard to install 
(need the right version of python) and does not work some of the new GPU cards.

The NMT external machine learner can be installed here 
https://github.com/tensorflow/nmt.
The parameters and scripts for training the model 
on GPU are given in the `src/nmt` directory.

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





