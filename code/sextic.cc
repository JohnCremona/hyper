#include <math.h>
#include <iostream>
using namespace std;

#include <pari/pari.h>

#define DEGREE 8
//#define DEGREE 6
//#define DEGREE 4
//#define DEGREE 2
#define ncoeffs (1+DEGREE)

void fill_all(double* ai, double c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] = c;
}

void scale(double* ai, double c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] *= c;
}

void assign(double* res, double* ai)
{
  for (int i=0; i<ncoeffs; i++)
    res[i] = ai[i];
}

void interleave(double* res, double* ai, double* bi)
{
  for (int i=0; i<ncoeffs; i++)   // ai[0], bi[1], ...
    res[i] = (i%2? bi[i] : ai[i]);
}

void split(double* res, double* ai, double* bi)
{
  for (int i=0; i<ncoeffs; i++)
    res[i] = (ai[i] + bi[i])/2;
}

double evaluate(double *ai, double x)
{
  double res=ai[0];
  for (int i=1; i<ncoeffs; i++)
    {
      res = res*x+ai[i];
    }
  return res;
}

// From Karim:

GEN
dbltorat(double x)
{
  pari_sp av = avma;
  GEN z;

  if (!x) return gen_0;

  z = utoi( dblmantissa(x) ); if (x < 0) setsigne(z, -1);
  return gerepileupto(av, gmul2n(z, dblexpo(x) - 63));
}

GEN dbltorat_old(double x) // assumes x=a/2^e
{
  if (x==0)
    {
      GEN res = cgetg(3, t_FRAC);
      gel(res,1) = stoi(0);
      gel(res,2) = stoi(1);
      return res;
    }
  long e;
  GEN num = mantissa_real(dbltor(x), &e);
  GEN den = int2n(e);
  return gdiv(num,den);
}

// global variables
GEN g0,g1,g2,g3,g4,g5,g6;
GEN f;
GEN dummy = stoi(0);

long pari_sturm(double *ai, int pos_only=0, int neg_only=0)
{
  if (0)
    {
      cout << "Coeffs are ";
      for(int i=0; i<ncoeffs; i++) cout<<ai[i]<<" ";
      cout<<endl;
    }
  // Only for quartics and sextics now!  since mkpoln needs all the coeffs individually.
  pari_sp av = avma;
  g0 = dbltorat(ai[0]);
  g1 = dbltorat(ai[1]);
  g2 = dbltorat(ai[2]);
#if DEGREE!=2
  g3 = dbltorat(ai[3]);
  g4 = dbltorat(ai[4]);
#if DEGREE==6
  g5 = dbltorat(ai[5]);
  g6 = dbltorat(ai[6]);
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4,g5,g6);
#else
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4);
#endif
#else
  f = mkpoln(ncoeffs,g0,g1,g2);
#endif
  f = gdiv(f,ggcd(f,derivpol(f)));
  long res;
  if (pos_only)
    res = sturmpart(f,gzero,NULL); // #roots >=0
  else
    {
      if (neg_only)
        res = sturmpart(f,NULL,gzero); // #roots <=0
      else
        res = sturm(f);                  // #roots
    }
  gerepileupto(av, dummy);
  return res;
}

int is_neg_def(double* ai, int pos_only=0, int neg_only=0)
{
  if (ai[0]>=0) return 0;      // f(0)>=0
  if (ai[DEGREE]>=0) return 0; // f(x)>=0 for |x| >>0
  double odds = 0, evens = 0;
  for (int i=0; i<ncoeffs; i++)
    if (i%2)
      odds += ai[i];
    else
      evens += ai[i];
  if (!neg_only)
    if ((evens+odds)>=0) return 0;  // f(1)  >=0
  if (!pos_only)
    if ((evens-odds)>=0) return 0;  // f(-1) >=0
  // now the leading coeff is negative so f(x) is neg def if it has no real roots:
  // use raandom tests first:
  int i;  double x;
  for (i=0, x=0.2; i<10; i++, x+=0.2)
    {
      if (!neg_only)
        if (evaluate(ai,x)>=0)
          return 0;
      if (!pos_only)
        if (evaluate(ai,-x)>=0)
          return 0;
    }

  return pari_sturm(ai, pos_only, neg_only)==0;
}

int is_pos_def(double* ai)
{
  double * minus_ai = new double[ncoeffs];
  assign(minus_ai, ai);
  scale(minus_ai,-1);
  int res = is_neg_def(minus_ai);
  delete[] minus_ai;
  return res;
}

/*
double *QuarticNDVolC(double tol, double *co1, double *co2, double v=0)
{
  int i, j;

  double *co3 = new double[ncoeffs];
  double *co4 = new double[ncoeffs];
  interleave(co3, co2, co1);
  interleave(co4, co1, co2);

  if (!v)
    {
      for (i=1, v=1; i<ncoeffs; i++)
        v *= (co2[i]-co1[i]);
    }

  double *res = new double[2];
  res[0] = res[1] = 0;
  // res[0] holds non neg def volume
  // res[1] holds neg def volume

  // quick exit if a>0 or e>0 or a+b+c+d+e>0 throughout:
  if (co1[0]>=0) return res;
  if (co1[DEGREE]>=0) return res;
  double odds = 0, evens1 = 0, evens2 = 0;
  for (int i=0; i<ncoeffs; i++)
    if (i%2)
      odds += co1[i];
    else
      {
        evens1 += co1[i];
        evens2 += co2[i];
      }
  if (((odds+evens1)>=0) ||  ((odds-evens2)>=0))
    {
      res[0]=v; return res;
    }

  if (is_neg_def(co2) &&  is_neg_def(co3))
    {
      res[1]=v; return res;
    }

  if (is_pos_def(co1) || is_pos_def(co4))
    {
      res[0]=v; return res;
    }

  double x=0.2;
  for (i=0; i<20; i++, x+=0.2)
    {
      if ( (evaluate(co1,x) >= 0) ||
           (evaluate(co4,x) >= 0) )
        {res[0]=v; return res;}
    }

  // add the range [0,v] if v is small
  if (v<tol)
    return res; // (0,0)

  // else recurse
  int twopower = 2<<ncoeffs;
  double v2 = v/twopower;
  split(co3, co1, co2);
  fill_all(co4, 0);
  double *new_co1 = new double[ncoeffs];
  double *new_co2 = new double[ncoeffs];
  double *res1;
  for (i=0; i<twopower; i++)
    {
      for (j=0; j<ncoeffs; j++)
        if (i&(2<<j))
          {new_co1[j]=co1[j]; new_co2[j]=co3[j];}
        else
          {new_co1[j]=co3[j]; new_co2[j]=co2[j];}

      res1 = QuarticNDVolC(tol, new_co1, new_co2, v2);
      res[0] += res1[0];
      res[1] += res1[1];
      delete[] res1;
    }
  delete[] co3, co4, new_co1, new_co2;
  return res;
}
*/

double *QND2(double tol, double *co1, double *co2, double v=0)
{
  int i;

  if (!v)
    {
      for (i=1, v=1; i<ncoeffs; i++)
        v *= (co2[i]-co1[i]);
    }

  double *res = new double[2];
  res[0] = res[1] = 0;
  // res[0] holds non neg def volume
  // res[1] holds neg def volume


  double *co3 = new double[ncoeffs]; // used for three temporary coeff lists
  interleave(co3, co2, co1);         // co2[0], co1[1], co2[2], ...

  // (1) the whole box is neg def iff (if co2<0 for all x>0, AND co3<0 for all x<0):

  if (    is_neg_def(co2, /* pos_only */ 1, /* neg_only */ 0)
      &&  is_neg_def(co3, /* pos_only */ 0, /* neg_only */ 1))
    {
      res[1]=v; return res;
    }

  // (2) the whole box is NOT neg def iff (if co1>0 for some x>0, OR co3>0 for some x<0)
  //                                  iff (co1 not neg def for x>0, OR c03 not neg def for x<0)

  interleave(co3, co1, co2);   // co1[0], co2[1], co1[2], ...
  if (   !is_neg_def(co1,  /* pos_only */ 1, /* neg_only */ 0)
      || !is_neg_def(co3,  /* pos_only */ 0, /* neg_only */ 1))
    {
      res[0]=v; return res;
    }

  // (3) Now this box is neither all in or all out. If its volume is
  // below our tolerance this volume is lost:

  if (v<tol)
    return res; // (0,0)

  // (4) Otherwise we divide up the box and recurse, divide a longest dimension by 2:
  double v2 = v/2;
  int j=0;
  double w=0, w2, f;
  for (i=0; i<ncoeffs; i++)
    {
      w2=co2[i]-co1[i];
      if (w2>w)
        {
          w=w2;
          j=i;
          f=(co1[i]+co2[i])/2;
        }
    }

  double *res1;
  assign(co3, co2);
  co3[j] = f;  // this is the mean of co1[j] and co2[j], otherwise co3=co2
  res1 = QND2(tol,co1,co3,v2);
  res[0] += res1[0];
  res[1] += res1[1];
  delete[] res1;

  assign(co3, co1);
  co3[j] = f;  // this is the mean of co1[j] and co2[j], otherwise co3=co1
  res1 = QND2(tol,co3,co2,v2);
  res[0] += res1[0];
  res[1] += res1[1];
  delete[] res1, co3;
  return res;
}

/*
void nonNDdensity(int logtol)
{
  int twopower = 2<<DEGREE;
  double tol = pow(2.0,-logtol);
  cout << "tolerance = "<<tol<<endl;
  double *ai = new double[ncoeffs];
  double *bi = new double[ncoeffs];
  fill_all(ai,-1); fill_all(bi,+1);
  ai[1] = 0;
  double *res = QuarticNDVolC(tol,ai,bi,twopower);
  cout << "res[0] = " << res[0] << ", res[1] = " << res[1] << endl;
  double nonND = res[0]/twopower;
  double ND = res[1]/twopower;
  delete[] ai, bi, res;
  cout << "lower bound = " << nonND << endl;
  cout << "upper bound = " << 1-ND << endl;
  double mid = (1-ND+nonND)/2;
  double wid = (1-ND-nonND)/2;
  cout << "middle value = " << mid << endl;
  cout << "error bound  = " << wid << endl;
}
*/

void nonNDdensity2(int logtol)
{
  int twopower = 1<< (DEGREE-2); // vol of quarter of half-box
  double tol = pow(2.0,-logtol);
  cout << "tolerance = "<<tol<<endl;
  double *ai = new double[ncoeffs];
  double *bi = new double[ncoeffs];
  fill_all(ai,-1); fill_all(bi,+1);
  ai[1] = 0; // switch x and -x; this defines the half-box
  bi[0] = bi[DEGREE] = 0;  // obvious condition, 3/4 of the half-box is certailny not ND
  double *res = QND2(tol,ai,bi,twopower);
  // res[0] holds non neg def volume
  // res[1] holds neg def volume
  cout << "res[0] = " << res[0] << ", res[1] = " << res[1] << endl;
  twopower *= 4;                        // allow for the other 3/4 of the half-box
  double nonND = 0.75 + res[0]/twopower;
  double ND = res[1]/twopower;
  delete [] ai, bi, res;
  cout << ND << " <= (neg.def.density) <= " << 1-nonND << endl;
  cout << "lower bound for non-neg def density  = " << nonND << endl;
  cout << "upper bound for non-neg def density  = " << 1-ND << endl;
  double mid = (1+nonND-ND)/2;
  double err = (1-nonND-ND)/2;
  cout << "middle value for non-neg def density = " << mid << endl;
  cout << "error bound for non-neg def density  = " << err << endl;
}


int main()
{
  pari_init(100000000,2);
  int logtol;
  cout << "Density of non-negative definite real polynomials of degree " << DEGREE << endl;
  cout << "Input log_2-tolerance: ";
  cin >> logtol;
  //nonNDdensity_shell(logtol);
  //nonNDdensity(logtol);
  nonNDdensity2(logtol);
}
