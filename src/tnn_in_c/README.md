This directory contains the implementation of a TNN with the mkl library.
The training data should be placed in a subdirectory named `data` with the following files:

- `arg.txt`: This file should contain the following pieces of information 
separated by a line break: 
  Line 1: number of operators
  

- `arity.txt`: Arity of each operators
- `dag.txt`,`dagi.txt`,`dago.txt`: This file contain the trees.
- `size.txt`: deprecated this contains the size of each tree.
- `obj.txt`,`obji.txt`,`objo.txt`: 
   This file contain objectives that each head must achieve.







The MKL code produces some OpenBlas code 
that may be called using the foreign function interface in Standard ML.
