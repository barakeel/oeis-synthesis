double *Acur;

void mv (const long dim, long arity, double A[], double X[], double Y[]) {
  long indim = arity * DIM + 1;
  cblas_dgemv (CblasRowMajor,CblasNoTrans,DIM,indim,1.0,A,indim,X,1,0.0,Y,1);
  }

void mv_head (const long dim, long out, double A[], double X[], double Y[]) {
  long indim = DIM + 1;
  cblas_dgemv (CblasRowMajor,CblasNoTrans,out,indim,1.0,A,indim,X,1,0.0,Y,1);
  }

void vtanh (const long dim, double Y[]) {
  for (long i = 0; i < dim; ++i) {Y[i] = tanh (Y[i]);}
  }

void fp_op (const long dim, long op, double X[], double Y[]) 
  {
  Acur = A + MO[op];
  if (HEAD[op] > 0) 
    {mv_head (dim, HEAD[op], Acur, X, Y); vtanh (HEAD[op],Y);}
  else if (ARITY[op] == 0) 
    {mv (dim,ARITY[op],Acur,X,Y);}
  else {mv (dim,ARITY[op],Acur,X,Y); vtanh (dim,Y);}
  }

int main () {return 0;};
