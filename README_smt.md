## Install

1. Install dependencies (estimated time: 10 min):
``` 
sudo apt install -y libgmp-dev rlwrap
sh install_dep_smt.sh
```

2. Install
```
cd src
sh install_smt.sh
```

## Starting the self-learning process
This system can train an external machine learner to provide induction schema instances to the SMT solver (Z3), enabling it to prove equalities between program pairs. Initial data is provided for starting this process.

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
where c1 and c2 are predicates produced during inference.

### Setting up the prover
1. Copy a binary of `z3` to the `src` directory and rename it to `z3`.

2. Create the directory `src/exp` and `src/exp/smt0`
   (Replace `smt0` by `smt4` if you are at the 5th iteration, etc) 

3. Copy the file produced during inference to `src/exp/smt0/input`.

4. Copy the file `http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/current` to  `src/exp/smt0/previous`.

5. You may edit the `config` file to change the number of cores `ncore`.

### Running the prover
1. Run the command `sh prove.sh smt0`.
2. Monitor the progress of the run in the directory 
   `src/exp/reserved_stringspec`.
3. This produces a file (after 3 hours) named `output`. 
It can be used to train the model for the next iteration (see self-learning and training).
4. This also produces a file named `current`. 
It is used to keep track of the solutions found up until that point.

### Self-Learning loop
You can repeat this process (training,inference,proving) 
many times starting from the newly created `output` file.
To keep previously found solutions, copy the `current` file from the 
directory of iteration `n` to the directory of iteration `n+1` and 
rename it to `previous`.
Ensure directory naming matches the iteration (`smt0`, `smt1`, etc).


