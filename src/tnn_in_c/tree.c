#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <mkl.h>
#include <math.h>
#include <string.h>
#define DIM 96
#define BUFFER 10000000
#define ALIGN 64
#define DBG 0
#define FIXED 0

// M is the number of lines (output), N is the number of column (input)
// DIM has to be bigger than maximum output dimension of heads
// HEADS are assumed to have arity 1 for now.

//shuffle
void swap(long *a, long *b) {
    long temp = *a;
    *a = *b;
    *b = temp;
}
void shuffle(long n ,long A[]) {
    srand(time(NULL));
    long i;
    for(i = n-1; i > 0; i--) {
        long j = rand() % (i+1);
        swap(&A[i], &A[j]);
    }
}

//reading input data
void read(const char* File, long A[]) {
  FILE *myFile;
  myFile = fopen(File, "r");
  long i = 0;
  char *line; 
  line = (char*)malloc (BUFFER);
  while (myFile && fgets(line,BUFFER,myFile)) {
    char* token = strtok(line, " ");
    while (token) {
      long num;
      if (sscanf(token, "%ld", &num) == 1) {A[i] = num; i++;}
     token = strtok(NULL, " ");
    }
  }
  free (line);
  }

// Warning: does scaling too
void read_double(const char* File, double A[]) {
  FILE *myFile;
  myFile = fopen(File, "r");
  long i = 0;
  char *line; 
  line = (char*)malloc (BUFFER);
  while (myFile && fgets(line,BUFFER,myFile)) {
    char* token = strtok(line, " ");
    while (token) {
      double d;
      if (sscanf(token, "%lf", &d) == 1) {A[i] = 2.0 * d - 1.0; i++;}
     token = strtok(NULL, " ");
    }
  }
  free (line);
  }

// Printing functions
void print_vecti (char *s, long size, long X[]) {
  printf("%s\n",s);
  for (long i = 0; i < size; ++i){printf("%li ", X[i]);}
  printf ("\n"); 
  }

void print_vect (char *s, long size, double X[]) {
  printf("%s\n",s);
  for (long i = 0; i < size; ++i){printf("%f ", X[i]);}
  printf ("\n"); 
  }

void print_mat (char *s, long n, long m, double A[]) {
  printf("%s\n",s);
  for (long i = 0; i < m*n; ++i)
    {printf("%.16f ",A[i]); if (i % n == n - 1) {printf("\n");}}
  }

void fprint_mat (FILE *locfp, char *s, long n, long m, double A[]) {
  fprintf(locfp,"%s\n",s);
  for (long i = 0; i < m*n; ++i)
    {fprintf(locfp,"%.16f ",A[i]); if (i % n == n - 1) {fprintf(locfp,"\n");}}
  }

// initialization
double randfrom(double min, double max) 
{
  double range = (max - min); 
  double div = RAND_MAX / range;
  return min + (rand() / div);
}

void rand_mat (long arity, double A[]) {
  long size = (arity * DIM + 1) * DIM;
  double coeff = sqrt (6.0 / ((arity * DIM + 1) + DIM));
  for (long i = 0; i < size; ++i) {A[i] = coeff * randfrom(-1.0, 1.0);}
  }

void fixed_mat (long arity, double A[]) {
  long size = (arity * DIM + 1) * DIM;
  for (long i = 0; i < size; ++i) {A[i] = 0.001 * i;}
  }

void rand_head (long out, double A[]) {
  long size = (DIM + 1) * out;
  double coeff = sqrt (6.0 / ((DIM + 1) + out));
  for (long i = 0; i < size; ++i) {A[i] = coeff * randfrom(-1.0, 1.0);}
  }

void fixed_head (long out, double A[]) {
  long size = (DIM + 1) * out;
  for (long i = 0; i < size; ++i) {A[i] = 0.001 * i;}
  }

void zero_vect (long size, double A[]) {
  for (long long i = 0; i < size; ++i) {A[i] = 0.0;}
  }

void zero_ivect (long size, long A[]) {
  for (long i = 0; i < size; ++i) {A[i] = 0;}
  }

void zero_mat (long arity, double A[]) {
  zero_vect ((arity * DIM + 1) * DIM, A);
  }

void zero_head (long out, double A[]) {
  zero_vect ((DIM + 1) * out, A);
  }

void copy (long n, double X[], double Y[]) {
  cblas_dcopy (n,X,1,Y,1);}
   
void one_vect (long size, double X[]) 
  {for (long i = 0; i < size; ++i) {X[i] = 1.0;}}

// computation
void tensor (double lr, long arity, double A[], double B[], double C[]) {
  long indim = arity * DIM + 1;
  cblas_dgemm
    (CblasRowMajor, CblasNoTrans, CblasNoTrans, 
     DIM, indim, 1, lr, A, 1, B, indim, 0.0, C, indim);
  if (DBG) {print_mat ("tensor",indim,DIM,C);}
  }

void mv (long arity, double A[], double X[], double Y[]) {
  long indim = arity * DIM + 1;
  if (DBG) {print_vect ("in",indim,X);}
  cblas_dgemv (CblasRowMajor,CblasNoTrans,DIM,indim,1.0,A,indim,X,1,0.0,Y,1);
  if (DBG) {print_vect ("out",DIM,Y);}
  }

void tmv (long arity, double A[], double X[], double Y[]) {
  long indim = arity * DIM + 1;
  if (DBG) {print_vect ("dout",DIM,X);}
  cblas_dgemv (CblasRowMajor,CblasTrans,DIM,indim,1.0,A,indim,X,1,0.0,Y,1);
  if (DBG) {print_vect ("din",indim,Y);}
  }

//same thing with special dimensions for the heads
void tensor_head (double lr, long out, double A[], double B[], double C[]) {
  long indim = DIM + 1;
  cblas_dgemm
    (CblasRowMajor, CblasNoTrans, CblasNoTrans, 
     out, indim, 1, lr, A, 1, B, indim, 0.0, C, indim);
  if (DBG) {print_mat ("tensor_head",indim,out,C);}
  }

void mv_head (long out, double A[], double X[], double Y[]) {
  long indim = DIM + 1;
  if (DBG) {print_vect ("in_head",indim,X);}
  cblas_dgemv (CblasRowMajor,CblasNoTrans,out,indim,1.0,A,indim,X,1,0.0,Y,1);
  if (DBG) {print_vect ("out_head",out,Y);}
  }

void tmv_head (long out, double A[], double X[], double Y[]) {
  long indim = DIM + 1;
  if (DBG) {print_vect ("dout",out,X);}
  cblas_dgemv (CblasRowMajor,CblasTrans,out,indim,1.0,A,indim,X,1,0.0,Y,1);
  if (DBG) {print_vect ("din",indim,Y);}
  }

// Update
void clip (long arity, double A[]) {
  for (long i = 0; i < (arity * DIM + 1)*DIM; ++i) {
    if (A[i] > 4.0) {A[i] = 4.0;}
    if (A[i] < -4.0) {A[i] = -4.0;}
    }
}

void clip_head (long out, double A[]) {
  for (long i = 0; i < (DIM + 1)*out; ++i) {
    if (A[i] > 4.0) {A[i] = 4.0;}
    if (A[i] < -4.0) {A[i] = -4.0;}
    }
}

void dtanh (long size, double C[], double X[], double Y[]) {
  if (DBG) {print_vect ("doutn",size,X);}
  for (long i = 0; i < size ; ++i) {
    double dtanh_temp = C[i]; 
    Y[i] = (1.0 - dtanh_temp * dtanh_temp) * X[i];
  }
}
  
int main()
  {
  // some indices
  long tmpex,ex,nex,dim,ep,op,opi,nop;
  long offset,sub,di,npolihead,nvaluehead;
  long sum,maxsize;
  double polierr, polierr2, valueerr;
  long a1, argi;
  long max_threads;
  // main arguments
  long ARG[7];

  // operators
  long *ARITY, *HEAD;
  long arity;
  
  // example structures
  long *SIZE, *SHF, *D, *DI, *OBJI;
  double *OBJ, *OBJcur;
  long *DO, *EXO, *OBJO;
  long dago, exo, objo;
  long *MO;
  long mo, mtot;
  
  
  
  // reading arguments
  read("data/arg.txt",ARG);
  nop = ARG[0];
  nex = ARG[1];
  dim = ARG[2];
  
  printf ("nop: %li\n", nop);
  printf ("nex: %li\n", nex);
  printf ("dim: %li\n", dim);
  
  // allocating operators/examples
  ARITY = (long*)mkl_malloc(nop*sizeof(long),ALIGN);
  MO = (long*)mkl_malloc(nop*sizeof(long),ALIGN);
  HEAD = (long*)mkl_malloc(nop*sizeof(long),ALIGN);
  SIZE = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  SHF = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  EXO = (long*)mkl_malloc(nex*sizeof(long),ALIGN);

  // reading operators/examples
  read("data/arity.txt",ARITY);
  read("data/head.txt",HEAD);
  read("data/size.txt",SIZE);
  
  // matrix offset based on arities
  mtot = 0;
  for (op=0; op < nop; ++op) {
    arity = ARITY[op];
    MO[op] = mtot;
    mtot += (arity * DIM + 1) * DIM;
  }
  
  // reading dag of examples
  sum = 0;
  for (ex = 0; ex < nex; ++ex) {sum += SIZE[ex];}
  printf("sum: %li\n", sum);
  maxsize = 0;
  for (ex = 0; ex < nex; ++ex) 
    {if (SIZE[ex] > maxsize) {maxsize = SIZE[ex];}}
  printf("maxsize: %li\n", maxsize);
  
  printf("reading examples\n");
  D = (long*)mkl_malloc(ARG[3]*sizeof(long),ALIGN);
  read("data/dag.txt",D);
  DO = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  read("data/dago.txt",DO);
  DI = (long*)mkl_malloc(ARG[4]*sizeof(long),ALIGN);
  read("data/dagi.txt",DI);
  printf("%li examples\n", nex);
  
  // offsets based on the number of operators per example
  EXO[0]=0;
  for (ex = 1; ex < nex; ++ex) {EXO[ex]=EXO[ex-1]+SIZE[ex-1];}
  
  // helping function for shuffling examples
  for (ex = 0; ex < nex; ++ex) {SHF[ex]=ex;}
  
  // total number of heads
  npolihead = 0; nvaluehead = 0;
  for (ex = 0; ex < nex; ++ex) {
    dago = DO[ex];
    exo = EXO[ex];
  for (sub = 0; sub < SIZE[ex]; ++sub) { 
    if (HEAD [D[dago + DI[exo + sub]]] == 1) {++nvaluehead;}
    if (HEAD [D[dago + DI[exo + sub]]] > 1) {++npolihead;}
  }}

  // potential objectives for each head in the dag
  printf("reading objectives\n");
  OBJ = (double*)mkl_malloc(ARG[5]*sizeof(double),ALIGN);
  read_double("data/obj.txt",OBJ);
  OBJO = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  read("data/objo.txt",OBJO);
  OBJI = (long*)mkl_malloc(ARG[6]*sizeof(long),ALIGN);
  read("data/obji.txt",OBJI);
  printf("%li %li objectives\n", nvaluehead, npolihead);

  //fixed biais for nullary operators
  double biais [1] = {1.0};

  //weights for each operator
  double *A, *Acur;
  A = (double*)mkl_malloc(mtot*sizeof( double ),ALIGN);
  for (op=0; op < nop; ++op) {
    if (HEAD[op] > 0) {
      if (FIXED) {fixed_head (HEAD[op],A+MO[op]);} else {rand_head (HEAD[op],A+MO[op]);}
      }
    else {
      if (FIXED) {fixed_mat (ARITY[op],A+MO[op]);} else {rand_mat (ARITY[op],A+MO[op]);}
      }
  }
  //printf("%li matrix initalized\n", nop);

  //update matrix for each operator
  double *U, *Ucur;
  U = (double*)mkl_malloc(mtot*sizeof( double ),ALIGN);
  void zeroU () {
  for (op=0; op < nop; ++op) {
    if (HEAD[op] == 0) {zero_mat (ARITY[op],U+MO[op]);}
    else {zero_head (HEAD[op],U+MO[op]);}
  }
  }
  zeroU ();
  //printf("%li update matrix zeroed\n", nop);
  
  //check if an operator was updated
  long *UPD;
  UPD = (long*)mkl_malloc(nop*sizeof( long ),ALIGN);

  //computation trace for each example
  long bY = DIM;
  double *X, *Y, *TY; 
  long *XI, *XSIZE;
  long xsize, opercount, xmax;
  XSIZE = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  XI = (long*)mkl_malloc(sum*sizeof(long),ALIGN);
  
  //Compute from arity and examples offsets for X
  xmax = 0;
  xsize = 0;
  opercount = 0;
  for (ex = 0; ex < nex; ++ex) {
    dago = DO[ex];
    exo = EXO[ex];
    xsize = 0;
    for (sub = 0; sub < SIZE[ex]; ++sub) {
      opi = dago + DI[exo + sub];
      op = D[opi];
      arity = ARITY[op];
      XI [opercount] = xsize;
      opercount++;
      xsize += arity * DIM + 1;
    }
    if (xsize > xmax) {xmax = xsize;}
    XSIZE [ex] = xsize;
  }
  
  // initalize memory
  double *Xcur, *Ycur, *TYcur;
  X = (double*)mkl_malloc(xmax*sizeof( double ),ALIGN);
  Y = (double*)mkl_malloc(bY*maxsize*sizeof( double ),ALIGN);
  TY = (double*)mkl_malloc(bY*maxsize*sizeof( double ),ALIGN);
  
  double *GX, *GY, *GTY;
  double *GXcur, *GYcur, *GTYcur;
  GX = (double*)mkl_malloc(xmax*sizeof( double ),ALIGN);
  GY = (double*)mkl_malloc(bY*maxsize*sizeof( double ),ALIGN);
  GTY = (double*)mkl_malloc(bY*maxsize*sizeof( double ),ALIGN);
  
  // setting the number of threads
  max_threads = mkl_get_max_threads();
  printf ("max_threads: %li\n", max_threads);
  mkl_set_num_threads(1);
  printf ("threads: %i\n", 1);
  //training
  long EP = 200; //nex=20;
  double lr = 0.0008;
  for (ep = 0; ep < EP; ++ep) {
  if (ep == 25) {lr = 0.0004;}
  if (ep == 50) {lr = 0.0002;}  
  if (ep == 75) {lr = 0.0001;}
  shuffle (nex,SHF);
  polierr = 0; polierr2 = 0; valueerr = 0;
  for (tmpex = 0; tmpex < nex; ++tmpex) {
    if (FIXED) {ex = tmpex;} else {ex = SHF[tmpex];}
    dago = DO[ex];
    exo = EXO[ex];
    objo = OBJO[ex];
    one_vect (XSIZE[ex],X); // could be done faster
    zero_vect (bY*SIZE[ex],GTY); //zeroing gradients of one example
    
  //forward pass
  if (DBG) {printf ("example size: %li\n", SIZE[ex]);}
  
  for (sub = 0; sub < SIZE[ex]; ++sub) {
    opi = dago + DI[exo + sub];
    op = D[opi];
    if (DBG) {printf ("oper: %li\n", op);}
    Xcur = X + XI[exo + sub];
    Ycur = Y + bY * sub;
    TYcur = TY + bY * sub;
    Acur = A + MO[op];
    if (HEAD[op] > 0) {
      copy (DIM, TY + bY * D[opi+1], Xcur);
      mv_head (HEAD[op], Acur, Xcur, Ycur);
      vdTanh (HEAD[op], Ycur, TYcur);
      }
    else if (ARITY[op] == 0) {
      mv (ARITY[op],Acur,biais,Ycur);
      copy (bY, Ycur, TYcur);
      }
    else
      {
      for (argi = 1; argi <= ARITY[op]; ++argi) 
        {copy (bY, TY + bY * D[opi+argi], Xcur + bY * (argi - 1));}
      mv (ARITY[op], Acur, Xcur, Ycur);
      vdTanh (bY,Ycur,TYcur);
      }
    if (DBG) {print_vect ("outn",bY,TYcur);}
  }//end forward pass

  //backward pass
  for (sub = SIZE[ex] - 1; sub >= 0; --sub) {
    opi = dago + DI[exo + sub];
    op = D[opi];
    Xcur = X + XI[exo + sub];
    Ycur = Y + bY * sub;
    TYcur = TY + bY * sub;
    GXcur = GX + XI[exo + sub];
    GYcur = GY + bY * sub;
    GTYcur = GTY + bY * sub;
    Acur = A + MO[op];
    if (HEAD[op] > 0) {
      OBJcur = OBJ + objo + OBJI[exo + sub];
      if (DBG) {print_vect ("expectv",HEAD[op],OBJcur);}
      vdSub (HEAD[op], OBJcur, TYcur, GTYcur);
      if (DBG) {print_vect ("diff",HEAD[op],GTYcur);}
      if (HEAD[op] == 1) 
        {valueerr += sqrt (cblas_ddot (HEAD[op],GTYcur,1,GTYcur,1));}
      else  {
           polierr += 
             sqrt (cblas_ddot (HEAD[op],GTYcur,1,GTYcur,1) / HEAD[op]);
           polierr2 += cblas_dasum (HEAD[op],GTYcur,1) / HEAD[op];
           }
      dtanh (HEAD[op], TYcur, GTYcur, GYcur);
      tmv_head (HEAD[op], Acur, GYcur, GXcur);
      a1 = bY * D[opi+1];
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      }
    else if (ARITY[op] == 0) {    
      copy (bY, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      }
    else {
      dtanh (bY, TYcur, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      for (argi = 1; argi <= ARITY[op]; ++argi) 
        {
        a1 = bY * D[opi+argi];
        vdAdd (bY, GTY + a1, GXcur + bY * (argi - 1) , GTY + a1);
        }
      }
  }//end backward pass
  
  //updates
  zero_ivect (nop,UPD);
  for (sub = SIZE[ex] - 1; sub >= 0; --sub) {
    opi = dago + DI[exo + sub];
    op = D[opi];
    UPD[op] = 1;
    Acur = A + MO[op];
    Ucur = U + MO[op];
    Xcur = X + XI[exo + sub];
    GYcur = GY + bY * sub;
    if (HEAD [op] > 0) {
      tensor_head (lr,HEAD[op],GYcur,Xcur,Ucur);
      vdAdd ((DIM+1)*HEAD[op],Acur,Ucur,Acur); 
      }
    else if (ARITY[op] == 0) {
      tensor (lr,ARITY[op],GYcur,biais,Ucur);
      vdAdd ((ARITY[op]*DIM+1)*DIM,Acur,Ucur,Acur);
      }
    else {
      tensor (lr,ARITY[op],GYcur,Xcur,Ucur);
      vdAdd ((ARITY[op]*DIM+1)*DIM,Acur,Ucur,Acur);
      }
  }

 //clipping
  if (ep % 10 == 9) {
  for (op = 0; op < nop; ++op) {
    if (UPD[op] > 0) {
    Acur = A + MO[op];
    if (HEAD [op] > 0) {clip_head (HEAD[op],Acur);
      if (DBG) {print_mat ("A",DIM+1,HEAD[op],Acur);}
      }
    else {clip (ARITY[op],Acur);
      if (DBG) {print_mat ("A",ARITY[op]*DIM+1,DIM,Acur);}
      }
    }
  }//end clipping
  }

  }//end example
  
  if (nvaluehead != 0) {printf("%li(v): %f\n", ep, valueerr / nvaluehead);}
  if (npolihead != 0) 
    {printf("%li: mse %f mae %f\n", ep, polierr / npolihead, 
             polierr2 / npolihead);}
  
  
  fflush(stdout);
  }//end training

  FILE *fp;
  // export to standard ml
  fp = fopen("out_sml", "w");
  fprintf(fp, "START MATRICES\n");
  for (op = 0; op < nop; ++op) {
    Acur = A + MO[op];
    if (HEAD [op] > 0) {fprint_mat (fp,"A",DIM+1,HEAD[op],Acur);}
    else {fprint_mat (fp,"A",ARITY[op]*DIM+1,DIM,Acur);}
  }
  fclose(fp);

  //export to openblas
  long i;

  fp = fopen("out_ob", "w");
  fprintf(fp, "double A[%li] = {", mtot);
  for (i = 0; i < mtot; i++)
    {
    fprintf(fp, "%.16f", A[i]);
    if (i < mtot - 1) {fprintf(fp, ", ");}
    else {fprintf(fp,"};\n");}
    }
  fprintf(fp, "long MO[%li] = {", nop);
  for (i = 0; i < nop; i++)
    {
    fprintf(fp, "%li", MO[i]);
    if (i < nop - 1) {fprintf(fp, ", ");}
    else {fprintf(fp,"};\n");}
    }
  fprintf(fp, "long HEAD[%li] = {", nop);
  for (i = 0; i < nop; i++)
    {
    fprintf(fp, "%li", HEAD[i]);
    if (i < nop - 1) {fprintf(fp, ", ");}
    else {fprintf(fp,"};\n");}
    }
  fprintf(fp, "long ARITY[%li] = {", nop);
  for (i = 0; i < nop; i++)
    {
    fprintf(fp, "%li", ARITY[i]);
    if (i < nop - 1) {fprintf(fp, ", ");}
    else {fprintf(fp,"};\n");}
    }
  fclose(fp);


return 0;
}