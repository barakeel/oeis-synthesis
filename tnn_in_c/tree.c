#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <mkl.h>
#include <math.h>
#include <string.h>
#define DIM 64
#define BUFFER 10000000
#define ALIGN 64
#define MAXARITY 5
// M is the number of lines (output), N is the number of column (input)
// DIM has to be bigger than maximum output dimension of heads


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
  for (long i = 0; i < size; ++i) {A[i] = 0.1;}
  }

void rand_head (long out, double A[]) {
  long size = (DIM + 1) * out;
  double coeff = sqrt (6.0 / ((DIM + 1) + out));
  for (long i = 0; i < size; ++i) {A[i] = coeff * randfrom(-1.0, 1.0);}
  }

void fixed_head (long out, double A[]) {
  long size = (DIM + 1) * out;
  for (long i = 0; i < size; ++i) {A[i] = 0.1;}
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
  //print_mat ("tensor",indim,DIM,C);
  }

void mv (long arity, double A[], double X[], double Y[]) {
  long indim = arity * DIM + 1;
  //print_vect ("in",indim,X);
  cblas_dgemv (CblasRowMajor,CblasNoTrans,DIM,indim,1.0,A,indim,X,1,0.0,Y,1);
  //print_vect ("out",DIM,Y);
  }

void tmv (long arity, double A[], double X[], double Y[]) {
  long indim = arity * DIM + 1;
  //print_vect ("dout",DIM,X);
  cblas_dgemv (CblasRowMajor,CblasTrans,DIM,indim,1.0,A,indim,X,1,0.0,Y,1);
  //print_vect ("din",indim,Y);
  }

//same thing with special dimensions for the heads
void tensor_head (double lr, long out, double A[], double B[], double C[]) {
  long indim = DIM + 1;
  cblas_dgemm
    (CblasRowMajor, CblasNoTrans, CblasNoTrans, 
     out, indim, 1, lr, A, 1, B, indim, 0.0, C, indim);
  //print_mat ("tensor",indim,out,C);
  }

void mv_head (long out, double A[], double X[], double Y[]) {
  long indim = DIM + 1;
  //print_vect ("in",indim,X);
  cblas_dgemv (CblasRowMajor,CblasNoTrans,out,indim,1.0,A,indim,X,1,0.0,Y,1);
  //print_vect ("out",out,Y);
  }

void tmv_head (long out, double A[], double X[], double Y[]) {
  long indim = DIM + 1;
  //print_vect ("dout",out,X);
  cblas_dgemv (CblasRowMajor,CblasTrans,out,indim,1.0,A,indim,X,1,0.0,Y,1);
  //print_vect ("din",indim,Y);
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
  //print_vect ("doutn",size,X);
  for (long i = 0; i < size ; ++i) {
    double dtanh_temp = C[i]; 
    Y[i] = (1.0 - dtanh_temp * dtanh_temp) * X[i];
  }
}

int main()
  {
  // some indices
  long tmpex,ex,nex,ep,op,nop;
  long offset,sub,di,nhead;
  long sum;
  double err;
  long a1,a2,a3,a4,a5;
  long max_threads;
  // main arguments
  long ARG[3];

  // operators
  long *ARITY, *HEAD;
  
  // example structures
  long *SIZE, *CUMUL, *SHF, *D;
  double *OBJ, *OBJcur;

  // reading arguments
  read("data/arg.txt",ARG);
  nop = ARG[0];
  nex = ARG[1];
  printf ("nop: %li\n", nop);
  printf ("nex: %li\n", nex);

  // allocating operators/examples
  ARITY = (long*)mkl_malloc(nop*sizeof(long),ALIGN);
  HEAD = (long*)mkl_malloc(nop*sizeof(long),ALIGN);
  SIZE = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  SHF = (long*)mkl_malloc(nex*sizeof(long),ALIGN);
  CUMUL = (long*)mkl_malloc(nex*sizeof(long),ALIGN);

  // reading operators/examples
  read("data/arity.txt",ARITY);
  read("data/head.txt",HEAD);
  read("data/size.txt",SIZE);
  
  // reading dag of examples
  sum = 0;
  for (ex = 0; ex < nex; ++ex) {sum += SIZE[ex];};
  printf("sum: %li\n", sum);
  long bD = MAXARITY + 1; // max argument plus one
  D = (long*)mkl_malloc(bD*sum*sizeof(long),ALIGN);
  read("data/dag.txt",D);
  nhead = 0;
  for (di = 0; di < sum; ++di) {
    if (HEAD [D[bD*di]] > 0) {++nhead;}
    }  
  printf("nhead: %li\n", nhead);
  CUMUL[0]=0;
  for (ex = 1; ex < nex; ++ex) {CUMUL[ex]=CUMUL[ex-1]+SIZE[ex-1];}
  for (ex = 0; ex < nex; ++ex) {SHF[ex]=ex;}

  
  // potential objectives for each head in the dag
  printf("allocating doubles\n");
  OBJ = (double*)mkl_malloc(DIM*sum*sizeof(double),ALIGN);
  printf("reading doubles\n");
  read_double("data/obj.txt",OBJ);  
  printf("success doubles\n");

  //fixed biais for nullary operators
  double biais [1] = {1.0};

  //weights for each operator
  long bA = (MAXARITY*DIM+1)*DIM;
  double *A, *Acur;
  A = (double*)mkl_malloc(bA*nop*sizeof( double ),ALIGN);
  for (op=0; op < nop; ++op) {
    if (HEAD[op] > 0) {
      //fixed_head (HEAD[op],A+bA*op);
      rand_head (HEAD[op],A+bA*op);
      }
    else {
      //fixed_mat (ARITY[op],A+op*bA);
      rand_mat (ARITY[op],A+op*bA);
      }
  }

  //update matrix for each operator
  double *U, *Ucur;
  U = (double*)mkl_malloc(bA*nop*sizeof( double ),ALIGN);
  void zeroU () {
  for (op=0; op < nop; ++op) {
    if (HEAD[op] == 0) {zero_mat (ARITY[op],U+op*bA);}
    else {zero_head (HEAD[op],U+bA*op);}
  }
  }
  zeroU ();

  //check if an operator was updated
  long *UPD;
  UPD = (long*)mkl_malloc(nop*sizeof( long ),ALIGN);

  //computation trace for each example
  long bX = MAXARITY*DIM+1;
  long bY = DIM;
  double *X, *Y, *TY; 
  double *Xcur, *Ycur, *TYcur;
  X = (double*)mkl_malloc(bX*sum*sizeof( double ),ALIGN);
  Y = (double*)mkl_malloc(bY*sum*sizeof( double ),ALIGN);
  TY = (double*)mkl_malloc(bY*sum*sizeof( double ),ALIGN);
  one_vect (bX*sum,X);

  double *GX, *GY, *GTY;
  double *GXcur, *GYcur, *GTYcur;
  GX = (double*)mkl_malloc(bX*sum*sizeof( double ),ALIGN);
  GY = (double*)mkl_malloc(bY*sum*sizeof( double ),ALIGN);
  GTY = (double*)mkl_malloc(bY*sum*sizeof( double ),ALIGN);
  
  // setting the number of threads
  max_threads = mkl_get_max_threads();
  printf ("max_threads: %li\n", max_threads);
  mkl_set_num_threads(1);
  printf ("threads: %i\n", 1);
  //training
  long EP = 200;
  double lr = 0.001;
  for (ep = 0; ep < EP; ++ep) {
  if (ep == 50) {lr = 0.0005;}
  if (ep == 100) {lr = 0.0002;}  
  if (ep == 150) {lr = 0.0001;}  
  shuffle (nex,SHF);
  zero_vect (bY*sum,GTY); //zeroing gradients of every examples
  err = 0;
  for (tmpex = 0; tmpex < nex; ++tmpex) {
    ex = SHF[tmpex];
    offset = CUMUL[ex];
  //forward pass
  for (sub = 0; sub < SIZE[ex]; ++sub) {
    di = offset + sub;
    op = D[bD*di];
    //printf ("oper: %li %li %li\n", op, D[bD*di+1], D[bD*di+2]);
    Xcur = X + bX * di;
    Ycur = Y + bY * di;
    TYcur = TY + bY * di;
    Acur = A + bA * op;
    if (HEAD[op] > 0) {
      a1 = D[bD*di+1];
      copy (DIM, TY + bY * (offset+a1), Xcur);
      mv_head (HEAD[op], Acur, Xcur, Ycur);
      vdTanh (HEAD[op],Ycur,TYcur);
      }
    else {switch(ARITY[op]){    
    case 0: 
      mv (ARITY[op],Acur,biais,Ycur);
      copy (bY, Ycur, TYcur);
      break; 
    case 1: 
      a1 = bY * (offset + D[bD*di+1]);
      copy (DIM, TY + a1, Xcur);
      mv (ARITY[op], Acur, Xcur, Ycur);
      vdTanh (bY,Ycur,TYcur);
      break;
    case 2:
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      copy (DIM, TY + a1, Xcur);
      copy (DIM, TY + a2, Xcur + bY);
      mv (ARITY[op], Acur, Xcur, Ycur);
      vdTanh (bY,Ycur,TYcur);
      break;
    case 3:
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      a3 = bY * (offset + D[bD*di+3]);
      copy (DIM, TY + a1, Xcur);
      copy (DIM, TY + a2, Xcur + bY);
      copy (DIM, TY + a3, Xcur + bY*2);
      mv (ARITY[op], Acur, Xcur, Ycur);
      vdTanh (bY,Ycur,TYcur);
      break;
    case 5:
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      a3 = bY * (offset + D[bD*di+3]);
      a4 = bY * (offset + D[bD*di+4]);
      a5 = bY * (offset + D[bD*di+5]);
      copy (DIM, TY + a1, Xcur);
      copy (DIM, TY + a2, Xcur + bY);
      copy (DIM, TY + a3, Xcur + bY*2);
      copy (DIM, TY + a4, Xcur + bY*3);
      copy (DIM, TY + a5, Xcur + bY*4);
      mv (ARITY[op], Acur, Xcur, Ycur);
      vdTanh (bY,Ycur,TYcur);
      break;
    default: break;  
    }}
    //print_vect ("outn",bY,TYcur);
  }//end forward pass

  //backward pass
  for (sub = SIZE[ex] - 1; sub >= 0; --sub) {
    di = offset + sub;
    op = D[bD*di];
    Xcur = X + bX * di;
    Ycur = Y + bY * di;
    TYcur = TY + bY * di;
    GXcur = GX + bX * di;
    GYcur = GY + bY * di;
    GTYcur = GTY + bY * di;
    Acur = A + bA * op;
    if (HEAD[op] > 0) {
      //print_vect ("expectv",HEAD[op],OBJ+ex);
      OBJcur = OBJ + DIM * di;
      vdSub (HEAD[op], OBJcur, TYcur, GTYcur);
      //print_vect ("diff",HEAD[op],GTYcur);
      err += sqrt (cblas_ddot (HEAD[op],GTYcur,1,GTYcur,1));
      dtanh (HEAD[op], TYcur, GTYcur, GYcur);
      tmv_head (HEAD[op], Acur, GYcur, GXcur);
      a1 = bY * (offset + D[bD*di+1]);
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      }
    else {switch(ARITY[op]){    
    case 0:
      copy (bY, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      break; 
    case 1:
      dtanh (bY, TYcur, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      a1 = bY * (offset + D[bD*di+1]);
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      break;
    case 2:
      dtanh (bY, TYcur, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      vdAdd (bY, GTY + a2, GXcur + bY, GTY + a2);
      break;
    case 3:
      dtanh (bY, TYcur, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      a3 = bY * (offset + D[bD*di+3]);
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      vdAdd (bY, GTY + a2, GXcur + bY, GTY + a2);
      vdAdd (bY, GTY + a3, GXcur + bY*2, GTY + a3);
      break;
    case 5:
      dtanh (bY, TYcur, GTYcur, GYcur);
      tmv (ARITY[op], Acur, GYcur, GXcur);
      a1 = bY * (offset + D[bD*di+1]);
      a2 = bY * (offset + D[bD*di+2]);
      a3 = bY * (offset + D[bD*di+3]);
      a4 = bY * (offset + D[bD*di+4]);
      a5 = bY * (offset + D[bD*di+5]);
      vdAdd (bY, GTY + a1, GXcur, GTY + a1);
      vdAdd (bY, GTY + a2, GXcur + bY, GTY + a2);
      vdAdd (bY, GTY + a3, GXcur + bY*2, GTY + a3);
      vdAdd (bY, GTY + a4, GXcur + bY*3, GTY + a4);
      vdAdd (bY, GTY + a5, GXcur + bY*4, GTY + a5);
    break;
    default: break;  
    }}
  }//end backward pass
  
  //updates
  zero_ivect (nop,UPD);
  for (sub = SIZE[ex] - 1; sub >= 0; --sub) {
    di = offset + sub;
    op = D[bD*di];
    UPD[op] = 1;
    Acur = A + bA * op;
    Ucur = U + bA * op;
    Xcur = X + bX * di;
    GYcur = GY + bY * di;
    if (HEAD [op] > 0) {
      tensor_head (lr,HEAD[op],GYcur,Xcur,Ucur);
      vdAdd ((DIM+1)*HEAD[op],Acur,Ucur,Acur); 
      }
    else {
      if (ARITY[op] == 0) {
        tensor (lr,ARITY[op],GYcur,biais,Ucur);
        vdAdd ((ARITY[op]*DIM+1)*DIM,Acur,Ucur,Acur);
        }
      else {
      tensor (lr,ARITY[op],GYcur,Xcur,Ucur);
      vdAdd ((ARITY[op]*DIM+1)*DIM,Acur,Ucur,Acur);
      }
    }
  }

 //clipping
  if (ep % 10 == 9) {
  for (op = 0; op < nop; ++op) {
    if (UPD[op] > 0) {
    Acur = A + bA * op;
    if (HEAD [op] > 0) {clip_head (HEAD[op],Acur);
      //print_mat ("A",DIM+1,HEAD[op],Acur);
      }
    else {clip (ARITY[op],Acur);
      //print_mat ("A",ARITY[op]*DIM+1,DIM,Acur);
      }
    }
  }//end clipping
  }

  }//end example
  
  printf("%li: %f\n", ep, err / nhead);
  fflush(stdout);
  }//end training

  FILE *fp;
  
  // export to standard ml
  fp = fopen("/home/user/oeis-synthesis/tnn_in_c/out_sml", "w");
  fprintf(fp, "START MATRICES\n");
  for (op = 0; op < nop; ++op) {
    Acur = A + bA * op;
    if (HEAD [op] > 0) {fprint_mat (fp,"A",DIM+1,HEAD[op],Acur);}
    else {fprint_mat (fp,"A",ARITY[op]*DIM+1,DIM,Acur);}
  }
  fclose(fp);


return 0;
}
