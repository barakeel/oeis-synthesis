## Install (includes polyml and hol)
This takes about 10 min to complete

``` 
sudo apt install -y libgmp-dev rlwrap
sh install_dep_smt.sh
cd src
sh install_smt.sh
```

## Starting the self-learning process
One can also trained an external machine learner to provide
instances of the induction schema to the SMT solver Z3 in order
to prove equalities between pairs of programs.

We provide the initial data from which the self-learning process 
can be started.

### Training 
For training, use as input the file 
`http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/output`.

Each line of file is of the form `p1=p2>c`
where p1=p2 is a proven equality and c is a predicate.

### Inference
For inference, use as input the file 
`http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/infer`.

Each line of the file is of the form `p1=p2` and 
should be completed to produce a file where each line has the form:
`p1=p2>c1|c2|...`
where c1 and c2 predicates produced during inference.

### Setting up the prover
- Copy a binary of `z3` to the `src` directory (name it `z3`)

- Create a directory `smt0` (you can choose what ever name you prefer) under the `exp` directory.

- Copy the file produced during inference to `exp/smt0/input`.

- Copy the file `http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/current` to 
`exp/yourexpname0/previous`

- You may edit the `config` file to change the number of cores `ncore` 

### Running the prover
Run the command `sh prove.sh smt0`.
This produces a file named `output`. 
It can be used to train the model for the next iteration (see self-learning and training).
This also produces a file named `current`. 
It is used to keep track of the solutions found up until that point.

### Self-Learning loop
You can repeat this process (training,inference,proving) 
many times starting from the newly created `output` file.
To keep previously found solutions, copy the `current` file from the 
directory of iteration `n` to the directory of iteration `n+1` and 
rename it to `previous`.
