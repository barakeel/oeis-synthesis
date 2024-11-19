## Install

1. Install dependencies (estimated time: 10 min)
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
At iteration 0, use as training examples the file 
`http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/output`.

At iteration 5 (for example), use the file `src/exp/smt4/output`.

Each line of file is of the form `p1=p2>c`
where p1=p2 is a proven equality and c is a predicate.

### Inference
In all iterations, use the file
`http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/infer`.

Each line of the file corresponds to a problem `p1=p2` and 
should be completed to produce a file where each line has the form:
`p1=p2>c1|c2|...`
where c1 and c2 are predicates produced during inference.

### Setting up the prover
1. Copy a binary of `z3` to the `src` directory and rename it to `z3`.

2. Create the directory `src/exp` and `src/exp/smt0`
   (Replace `smt0` by `smt5` if you are at iteration 5, etc) 

3. Copy the file produced during inference to `src/exp/smt0/input`.

4. At iteration 0, copy the file `http://grid01.ciirc.cvut.cz/~thibault/smt_rl0/current` to `src/exp/smt0/previous`.
   At iteration 5 (for example), copy the file `src/exp/smt4/current` to `src/exp/smt5/previous`.

5. You may edit the `config` file to change the number of cores `ncore`.

### Running the prover
1. Run the command `sh prove.sh smt0`.
2. Monitor the progress of the run in the directory 
   `src/exp/reserved_stringspec`.
3. After approximately 3 hours, the script output the file:
   - `src/exp/smt0/output`: training examples for the next iteration.
   - `src/exp/smt0/current`: tracks solutions found up until that point.

### Self-Learning loop
To continue the self-learning process:

1. Use the `src/exp/smtN/output` file from iteration `n` as the training data for iteration `n+1`.

2. Copy the current file from iteration `n` to the previous file for iteration `n+1`:

```
src/exp/smtN/current -> src/exp/smtN+1/previous
```

3. Ensure directory naming matches the iteration (`smt0`, `smt1`, etc.).


