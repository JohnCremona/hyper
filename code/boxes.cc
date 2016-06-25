#include <math.h>
#include <iostream>
using namespace std;

double i4(double a, double b, double c, double d, double e)
{
  return 12*a*e-3*b*d+c*c;
}

double j4(double a, double b, double c, double d, double e)
{
  return 72*a*c*e+9*b*c*d-27*a*d*d-27*e*b*b-2*c*c*c;
}

double h4(double a, double b, double c)
{
  return 8*a*c-3*b*b;
}

double q4(double a, double b, double c, double d, double e)
{
  return 3*b*b*b*b + 16*(a*a*(c*c+b*d)-a*b*b*c) - 64*a*a*a*e;
}

double disc4(double a, double b, double c, double d, double e)
{
  double i = i4(a,b,c,d,e);
  double j = j4(a,b,c,d,e);
  return 4*i*i*i-j*j;
}

int is_quartic_neg_def(double a, double b, double c, double d, double e)
{
  if ((a>=0) || (e>=0) || ((a+b+c+d+e)>=0) or ((a-b+c-d+e)>=0))
    {return 0;}
  if (disc4(a,b,c,d,e) <= 0)
    {return 0;}
  // now D>0, we require H>0 or Q<0
  return (h4(a,b,c) >= 0) || (q4(a,b,c,d,e) <= 0);
}

double **make_box(double a1, double b1, double c1, double d1, double e1, double a2, double b2, double c2, double d2, double e2)
{
  double **B = new double*[5];
  for (int i=0; i<5; i++) {B[i] = new double[2];}
  B[0][0] = a1;  B[0][1] = a2;
  B[1][0] = b1;  B[1][1] = b2;
  B[2][0] = c1;  B[2][1] = c2;
  B[3][0] = d1;  B[3][1] = d2;
  B[4][0] = e1;  B[4][1] = e2;
  return B;
}

void del_box(double** B)
{
  for (int i=0; i<5; i++) {delete[] B[i];}
  delete[] B;
}

double *QuarticNDVolC(double tol, double **B, double v=0)
{
  if (!B)
    B = make_box(-1,-1,-1,-1,-1,1,1,1,1,1);

  double a1 = B[0][0];
  double b1 = B[1][0];
  double c1 = B[2][0];
  double d1 = B[3][0];
  double e1 = B[4][0];
  double a2 = B[0][1];
  double b2 = B[1][1];
  double c2 = B[2][1];
  double d2 = B[3][1];
  double e2 = B[4][1];

  if (!v)
    v = (a2-a1)*(b2-b1)*(c2-c1)*(d2-d1)*(e2-e1);

  double *res = new double[2], *res1;
  res[0] = res[1] = 0;
  // res[0] holds non neg def volume
  // res[1] holds neg def volume

  // quick exit if a>0 or e>0 or a+b+c+d+e>0 throughout:
  if ((a1 >=0) || (e1 >=0) || ((a1+b1+c1+d1+e1) >=0) || ((a1-b2+c1-d2+e1)>=0))
    {res[0]=v; return res;}

  if (is_quartic_neg_def(a2,b2,c2,d2,e2) &&
      is_quartic_neg_def(a2,b1,c2,d1,e2))
    {
      res[1]=v; return res;
    }

  if (is_quartic_neg_def(-a1,-b1,-c1,-d1,-e1) ||
      is_quartic_neg_def(-a1,-b2,-c1,-d2,-e1))
    {
      res[0]=v; return res;
    }

  int i;  double x=0.2;
  for (i=0; i<20; i++, x+=0.2)
    {
      if ( ((((a1*x+b1)*x+c1)*x+d1)*x+e1 >= 0) ||
           ((((a1*x-b2)*x+c1)*x-d2)*x+e1 >= 0))
        {res[0]=v; return res;}
    }

  // add the range [0,v] if v is small
  if (v<tol)
    return res; // (0,0)

  // else recurse
  double v2 = v/32;
  double a3=(a1+a2)/2;
  double b3=(b1+b2)/2;
  double c3=(c1+c2)/2;
  double d3=(d1+d2)/2;
  double e3=(e1+e2)/2;
  double **subB = make_box(0,0,0,0,0,0,0,0,0,0);
  for (i=0; i<32; i++)
    {
      if (i&1)
        {subB[0][0]=a1; subB[0][1]=a3;}
      else
        {subB[0][0]=a3; subB[0][1]=a2;}
      if (i&2)
        {subB[1][0]=b1; subB[1][1]=b3;}
      else
        {subB[1][0]=b3; subB[1][1]=b2;}
      if (i&4)
        {subB[2][0]=c1; subB[2][1]=c3;}
      else
        {subB[2][0]=c3; subB[2][1]=c2;}
      if (i&8)
        {subB[3][0]=d1; subB[3][1]=d3;}
      else
        {subB[3][0]=d3; subB[3][1]=d2;}
      if (i&16)
        {subB[4][0]=e1; subB[4][1]=e3;}
      else
        {subB[4][0]=e3; subB[4][1]=e2;}
      res1 = QuarticNDVolC(tol,subB,v2);
      res[0] += res1[0];
      res[1] += res1[1];
      delete[] res1;
    }
  del_box(subB);
  return res;
}

double *QND2(double tol, double **B, double v=0)
{
  if (!B)
    B = make_box(-1,-1,-1,-1,-1,1,1,1,1,1);

  double a1 = B[0][0];
  double b1 = B[1][0];
  double c1 = B[2][0];
  double d1 = B[3][0];
  double e1 = B[4][0];
  double a2 = B[0][1];
  double b2 = B[1][1];
  double c2 = B[2][1];
  double d2 = B[3][1];
  double e2 = B[4][1];

  if (!v)
    v = (a2-a1)*(b2-b1)*(c2-c1)*(d2-d1)*(e2-e1);

  double *res = new double[2], *res1;
  res[0] = res[1] = 0;
  // res[0] holds non neg def volume
  // res[1] holds neg def volume

  // quick exit if a>0 or e>0 or a+b+c+d+e>0 throughout:
  if ((a1 >=0) || (e1 >=0) || ((a1+b1+c1+d1+e1) >=0) || ((a1-b2+c1-d2+e1)>=0))
    {res[0]=v; return res;}

  if (is_quartic_neg_def(a2,b2,c2,d2,e2) &&
      is_quartic_neg_def(a2,b1,c2,d1,e2))
    {
      res[1]=v; return res;
    }

  if (is_quartic_neg_def(-a1,-b1,-c1,-d1,-e1) ||
      is_quartic_neg_def(-a1,-b2,-c1,-d2,-e1))
    {
      res[0]=v; return res;
    }

  int i;  double x=0.2;
  for (i=0; i<20; i++, x+=0.2)
    {
      if ( ((((a1*x+b1)*x+c1)*x+d1)*x+e1 >= 0) ||
           ((((a1*x-b2)*x+c1)*x-d2)*x+e1 >= 0))
        {res[0]=v; return res;}
    }

  // add the range [0,v] if v is small
  if (v<tol)
    return res; // (0,0)

  // else recurse (divide a longest dimension by 2)
  double v2 = v/2;
  int j=1;
  double w=a2-a1, w2, f=(a1+a2)/2;
  w2=b2-b1; if (w2>w) {w=w2; j=2; f=(b1+b2)/2;}
  w2=c2-c1; if (w2>w) {w=w2; j=3; f=(c1+c2)/2;}
  w2=d2-d1; if (w2>w) {w=w2; j=4; f=(d1+d2)/2;}
  w2=e2-e1; if (w2>w) {w=w2; j=5; f=(e1+e2)/2;}
  double **B1, **B2;
  if (j==1)
    {
      B1 = make_box(a1,b1,c1,d1,e1,f,b2,c2,d2,e2);
      B2 = make_box(f,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    }
  else if (j==2)
    {
      B1 = make_box(a1,b1,c1,d1,e1,a2,f,c2,d2,e2);
      B2 = make_box(a1,f,c1,d1,e1,a2,b2,c2,d2,e2);
    }
  else if (j==3)
    {
      B1 = make_box(a1,b1,c1,d1,e1,a2,b2,f,d2,e2);
      B2 = make_box(a1,b1,f,d1,e1,a2,b2,c2,d2,e2);
    }
  else if (j==4)
    {
      B1 = make_box(a1,b1,c1,d1,e1,a1,b2,c2,f,e2);
      B2 = make_box(a1,b1,c1,f,e1,a2,b2,c2,d2,e2);
    }
  else if (j==5)
    {
      B1 = make_box(a1,b1,c1,d1,e1,a1,b2,c2,d2,f);
      B2 = make_box(a1,b1,c1,d1,f,a2,b2,c2,d2,e2);
    }

  res1 = QuarticNDVolC(tol,B1,v2);
  res[0] += res1[0];
  res[1] += res1[1];
  delete[] res1;
  res1 = QuarticNDVolC(tol,B2,v2);
  res[0] += res1[0];
  res[1] += res1[1];
  delete[] res1;
  del_box(B1);
  del_box(B2);
  return res;
}

void nonNDdensity(int logtol)
{
  double tol = pow(2.0,-logtol);
  cout << "tolerance = "<<tol<<endl;
  double **B = make_box(-1,0,-1,-1,-1,1,1,1,1,1);
  double *res = QuarticNDVolC(tol,B,16);
  cout << "res[0] = " << res[0] << ", res[1] = " << res[1] << endl;
  double nonND = res[0]/16; //32;
  double ND = res[1]/16; //32;
  cout << "lower bound = " << nonND << endl;
  cout << "upper bound = " << 1-ND << endl;
  double mid = (1-ND+nonND)/2;
  double wid = (1-ND-nonND)/2;
  cout << "middle value = " << mid << endl;
  cout << "error bound  = " << wid << endl;
}

void nonNDdensity2(int logtol)
{
  double tol = pow(2.0,-logtol);
  cout << "tolerance = "<<tol<<endl;
  double **B = make_box(-1,0,-1,-1,-1,1,1,1,1,1);
  double *res = QND2(tol,B,16);
  cout << "res[0] = " << res[0] << ", res[1] = " << res[1] << endl;
  double nonND = res[0]/16; //32;
  double ND = res[1]/16; //32;
  cout << "lower bound = " << nonND << endl;
  cout << "upper bound = " << 1-ND << endl;
  double mid = (1-ND+nonND)/2;
  double wid = (1-ND-nonND)/2;
  cout << "middle value = " << mid << endl;
  cout << "error bound  = " << wid << endl;
}

void nonNDdensity_shell(int logtol)
{
  double tol = pow(2.0,-logtol);
  cout << "tolerance = "<<tol<<endl;
  double **B;
  double *res = new double[2];
  double *xi = new double[5];
  int i,j,i0,i1,i2,i3,i4,n=0;
  res[0] = res[1] = 0;
  for (i=0; i<5; i++)
    {
      xi[i]=-1+i*0.5;
    }
  // Symmetries: both (b,d) --> (-b,-d) and (b,d) --> (d,b) do not
  // change the negative definiteness, so we may assume both b>0 and
  // d>0 and multiply by 4.  In this model this means that we omit j
  // when i1<2 or i3<2.
  int sym_factor = 2;//4;
  for (j=0; j<1024; j++)
    {
      //cout << "j="<<j<<": ";
      i1 = (j&12)>>2;     if (i1<2) continue;
      i3 = (j&192)>>6; //   if (i3<2) continue;
      i0 = j&3;
      i2 = (j&48)>>4;
      i4 = (j&768)>>8;
      //cout<<i0<<","<<i1<<","<<i2<<","<<i3<<","<<i4<<endl;
      if (i0+4*i1+16*i2+64*i3+256*i4 != j)
        cout << "error in converting j = " << j << endl;
      if ( ! ( ((xi[i0]==0)||(xi[i0+1]==0)) && ((xi[i1]==0)||(xi[i1+1]==0)) &&
               ((xi[i2]==0)||(xi[i2+1]==0)) && ((xi[i3]==0)||(xi[i3+1]==0)) &&
               ((xi[i4]==0)||(xi[i4+1]==0)) ) )
        {
          n +=1;
          //cout << "Box corners: ("<<xi[i0]<<","<<xi[i1]<<","<<xi[i2]<<","<<xi[i3]<<","<<xi[i4]<<"), ("<<xi[i0+1]<<","<<xi[i1+1]<<","<<xi[i2+1]<<","<<xi[i3+1]<<","<<xi[i4+1]<<")"<<endl;
          //cout << "b-range: ("<<xi[i1]<<","<<xi[i1+1]<<")"<<"\t";
          //cout << "d-range: ("<<xi[i3]<<","<<xi[i3+1]<<")"<<endl;
          B = make_box(xi[i0],xi[i1],xi[i2],xi[i3],xi[i4],
                       xi[i0+1],xi[i1+1],xi[i2+1],xi[i3+1],xi[i4+1]);
          double *res1 = QuarticNDVolC(tol,B,1.0/32);
          del_box(B);
          res[0] += res1[0];
          res[1] += res1[1];
          delete[] res1;
        }
      }
  if (n!=(1024-32)/sym_factor)
    {
      cout << n << " sub-boxes used (should be "
           << (1024-32)/sym_factor << ")" << endl;
    }
  cout << "res[0] = " << res[0] << ", res[1] = " << res[1] << endl;
  double nonND = sym_factor*res[0]/31;
  double ND = sym_factor*res[1]/31;
  cout << "lower bound = " << nonND << endl;
  cout << "upper bound = " << 1-ND << endl;
  double mid = (1-ND+nonND)/2;
  double wid = (1-ND-nonND)/2;
  cout << "middle value = " << mid << endl;
  cout << "error bound  = " << wid << endl;
}

int main()
{
  int logtol;
  cout << "Input log_2-tolerance: ";
  cin >> logtol;
  //nonNDdensity_shell(logtol);
  //nonNDdensity(logtol);
  nonNDdensity2(logtol);
}
