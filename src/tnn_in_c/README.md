This directory contains the implementation of a TNN with the mkl library.
The training data should be placed in a subdirectory named `data` with the following files:

- `arg.txt`: This file should contain the following pieces of information 
separated by a line break: 
  Line 1: number of operators
  

- `arity.txt`: The arity of each operators
- `dag.txt`: 
  This file contains one example per line. 
  Each example is a list of tokens where each token is followed 
  by the indices of its arguments.
- `size.txt`: The size of each example in number of tokens (excluding arguments).
- `obj.txt`: This file contain objectives that each head must achieve in the order they appear in the dag file. Objectives are vectors of real numbers between 0.0 and 1.0. A scaling is done by read_double to match tanh codomain 
so the output that produced by the trained network is actually between -1.0 and 1.0 and needs to be rescaled back.
The size of each objective vector is 0 for operators that are not head and is given in the file `head.txt`. In case of a policy this corresponds to the number of actions. Finally all the objectives are concatenated in the files `obj.txt`

Given a token number, the "i" files tells the offset (in number of tokens + arguments) necessary to reach that token. 
Given an example number, the "o" files tells the offset (in number of tokens + arguments) necessary to reach that example.

The MKL code produces some OpenBlas code 
that may be called using the foreign function interface in Standard ML.
