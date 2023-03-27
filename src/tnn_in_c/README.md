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
- `obj.txt`: This file contain objectives that each head must achieve in the order they appear in the dag file.


Given a token number, the "i" files tells the argument offset 
necessary to reach that token. 
Given an example, the "o" files tells the offset necessary to reach that example.



The MKL code produces some OpenBlas code 
that may be called using the foreign function interface in Standard ML.
