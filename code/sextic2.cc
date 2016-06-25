# Version using integers only, no doubles, and libpari
#
#include <math.h>
#include <iostream>
using namespace std;

#include <pari/pari.h>

//#define DEBUG

#define DEGREE 10
//#define DEGREE 8
//#define DEGREE 6
//#define DEGREE 4
//#define DEGREE 2
#define ncoeffs (1+DEGREE)

void fill_all(long* ai, long c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] = c;
}

void scale(long* ai, long c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] *= c;
}

void assign(long* res, long* ai)
{
  for (int i=0; i<ncoeffs; i++)
    res[i] = ai[i];
}

void interleave(long* res, long* ai, long* bi)
{
  for (int i=0; i<ncoeffs; i++)   // ai[0], bi[1], ...
    res[i] = (i%2? bi[i] : ai[i]);
}

long evaluate(long *ai, long x)
{
  long res=ai[0];
  for (int i=1; i<ncoeffs; i++)
    res = res*x+ai[i];
  return res;
}

long volume(long* ai, long* bi)
{
  long v=1;
  for (int i=0; i<ncoeffs; i++)
    v *= (bi[i] - ai[i]);
  return v;
}

void print_coeffs(long *ai)
{
  for (int i=0; i<ncoeffs; i++)
    {
      if(i) cout<<" ";
      cout<<ai[i];
    }
}

void show_box(long *ai, long *bi)
{
  cout << "ai: "; print_coeffs(ai); cout << endl;
  cout << "bi: "; print_coeffs(bi); cout << endl;
}

// global variables
GEN g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12;
GEN f;
GEN dummy = stoi(0);

long pari_sturm(long *ai, int pos_only=0, int neg_only=0)
// Return the number of real roots (default), number of positive real
// roots (if pos_only==1) or number of negative real roots (if
// neg_only==1)
{
  // Only for degrees 2, 4, 6 so far, since mkpoln needs all the coeffs individually.
  long res;
  pari_sp av = avma;
  g0 = stoi(ai[0]);
  g1 = stoi(ai[1]);
  g2 = stoi(ai[2]);
#if DEGREE==2
  f = mkpoln(ncoeffs,g0,g1,g2);
#else
  g3 = stoi(ai[3]);
  g4 = stoi(ai[4]);
#if DEGREE==4
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4);
#else
  g5 = stoi(ai[5]);
  g6 = stoi(ai[6]);
#if DEGREE==6
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4,g5,g6);
#else
  g7 = stoi(ai[7]);
  g8 = stoi(ai[8]);
#if DEGREE==8
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4,g5,g6,g7,g8);
#else
  g9 = stoi(ai[9]);
  g10 = stoi(ai[10]);
#if DEGREE==10
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10);
#else
  g11 = stoi(ai[11]);
  g12 = stoi(ai[12]);
  f = mkpoln(ncoeffs,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12);
#endif
#endif
#endif
#endif
#endif
  f = gdiv(f,ggcd(f,derivpol(f)));

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


int is_neg_def(long* ai, int pos_only=0, int neg_only=0)
// Return 1 iff the poly with coeffs ai is negative definite, by
// default for all x in R; if pos_only==1 then test only for x>=0, and
// if neg_only=1 then test only for x<=0.
#if DEGREE==2
{
  if (ai[0]>=0) return 0;      // f(0)>=0
  if (ai[DEGREE]>=0) return 0; // f(x)>=0 for |x| >>0
  long b = ai[1];
  if (b*b < 4*ai[0]*ai[2]) return 1; // f is neg def
  if (pos_only) return (b<0);
  if (neg_only) return (b>0);
  return 0;
}
#else // generic code for any degree
{
  if (ai[0]>=0) return 0;      // f(0)>=0
  if (ai[DEGREE]>=0) return 0; // f(x)>=0 for |x| >>0
  long odds = 0, evens = 0;  // sums of odd/even indexed coefficients
  for (int i=0; i<ncoeffs; i++)
    if (i%2)
      odds += ai[i];
    else
      evens += ai[i];
  if (!neg_only)          // test if f(1)  >=0
    if ((evens+odds)>=0) return 0;
  if (!pos_only)          // test if f(-1)  >=0
    if ((evens-odds)>=0) return 0;

  // now the leading coeff is negative so f(x) is neg def if it has no real roots:

  return pari_sturm(ai, pos_only, neg_only)==0;
}
#endif

void QND(int depth, long *co1, long *co2, double& non, double& neg)
// co1, co2 hold the coefficients of two polynomials at extreme
// corners, with co1[i]<co2[i] for all i.  Recurse (with depth
// incremented) unless depth>=0.  non is the fraction of this box
// proved not negative definite, neg is the fraction proved negative
// definite.
{
#ifdef DEBUG
  cout << "Box at depth " <<depth<<":"<<endl;
  show_box(co1,co2);
#endif
  int i,j;

  non = 0.0; // on return, holds (lower bound for) non neg def density
  neg = 0.0; // on return, holds (lower bound for) neg def density

  long *co3 = new long[ncoeffs]; // used for temporary coeff lists

  interleave(co3, co2, co1);         // co2[0], co1[1], co2[2], ...
#ifdef DEBUG
  cout << "(a)"<<endl;
  show_box(co1,co2);
#endif

  // (1) the whole box is neg def iff
  //
  // ((co2(x)<0 for all x>0) AND (co3(x)<0 for all x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies f(x) < co3(x)

  if (    is_neg_def(co2, /* pos_only */ 1, /* neg_only */ 0)
      &&  is_neg_def(co3, /* pos_only */ 0, /* neg_only */ 1))
    {
#ifdef DEBUG
      cout << "all negative definite" << endl;
#endif
      neg=1.0; delete[] co3; return;
    }
#ifdef DEBUG
  cout << "(b)"<<endl;
  show_box(co1,co2);
#endif


  interleave(co3, co1, co2);   // co1[0], co2[1], co1[2], ...
#ifdef DEBUG
  cout << "(c)"<<endl;
  show_box(co1,co2);
#endif

  // (2) the whole box is NOT neg def iff
  //
  // ((co1(x)>0 for some x>0) OR (co3(x)>0 for some x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies co3(x) < f(x)

  if (   !is_neg_def(co1,  /* pos_only */ 1, /* neg_only */ 0)
      || !is_neg_def(co3,  /* pos_only */ 0, /* neg_only */ 1))
    {
#ifdef DEBUG
      cout << "none negative definite" << endl;
#endif
      non=1.0; delete[] co3; return;
    }
#ifdef DEBUG
  cout << "(d)"<<endl;
  show_box(co1,co2);
#endif

  // (3) Now this box is neither all in nor all out. If the maximum
  // recursion depth has been reached, its volume will be lost to the
  // error term, as both non and neg are 0.

  if (depth>=0)
    {
#ifdef DEBUG
      cout << "reached max depth" << endl;
#endif
      delete[] co3; 
      return;
    }

#ifdef DEBUG
      cout << "recursing..." << endl;
#endif

  // (4) Otherwise we cut the box in 2 (dividing a longest dimension
  // by 2) and recurse.  The values of non and neg are the means of
  // those in the two sub-boxes.  To keep integer coefficients we
  // double all coordinates if necessary, which does not affect the
  // densities.

  j=0; // index of longest box edge
  long w; // holds length of longest box edge
  long w2;
  // initialise:
  w=co2[0]-co1[0];
  // look for a longer edge:
  for (i=1; i<ncoeffs; i++)
    {
      w2=co2[i]-co1[i];
      if (w2>w) // i'th dimension is greater, so update
        {
          w=w2;
          j=i;
        }
    }

#ifdef DEBUG
  cout << "(e)"<<endl;
  show_box(co1,co2);
#endif

  long f=co1[j]+co2[j];
  // double both co1, co2 unless f is even:
  long *sco1 = new long[ncoeffs]; // to store scaled coeff lists
  long *sco2 = new long[ncoeffs]; // 
  assign(sco1, co1);
  assign(sco2, co2);
  if (f%2) // f is odd
    {
      scale(sco1,2);
      scale(sco2,2);
#ifdef DEBUG
      cout << "(f: *2)"<<endl;
      show_box(sco1,sco2);
#endif
    }
  else // f is even
    {
      f /= 2;
    }
#ifdef DEBUG
  if (2*f!=(sco1[j]+sco2[j])) cout<<"!!! (1)"<<endl;
#endif
  // so now f == (co1[j]+co2[j])/2 and is integral in both cases

  // first sub-box: co3 is the same as co2 except for the j'th entry which is the mean
  assign(co3, sco2);
  co3[j] = f;
  double non1, neg1;
  QND(depth+1, sco1, co3, non1, neg1);
#ifdef DEBUG
  long vol = volume(sco1,sco2);
  long vol1 = volume(sco1,co3);
  if (2*vol1!=vol)
    {
      cout<<"!!! (2)"<<endl;
      cout<<"current box (scaled) = \n";show_box(sco1,sco2);cout<<"with volume "<<vol<<endl;
      cout<<"sub box 1 = \n";show_box(sco1,co3);cout<<"with volume "<<vol1<<endl;
    }
#endif

  // second sub-box: co3 is the same as co1 except for the j'th entry which is the mean
  assign(co3, sco1);
  co3[j] = f;
  double non2, neg2;
  QND(depth+1, co3, sco2, non2, neg2);
#ifdef DEBUG
  long vol2 = volume(co3,sco2);
  if (2*vol2!=vol)
    {
      cout<<"!!! (3)"<<endl;
      cout<<"current box = \n";show_box(sco1,sco2);cout<<"with volume "<<vol<<endl;
      cout<<"sub box 2 = \n";show_box(co3,sco2);cout<<"with volume "<<vol2<<endl;
    }
  if (vol2!=vol1) cout<<"!!! (4)"<<endl;
#endif

  non = (non1+non2)/2.0; // average over two equal subvolumes
  neg = (neg1+neg2)/2.0; // average over two equal subvolumes

  delete[] co3;
  delete[] sco1;
  delete[] sco2;
}

void nonNDdensity2(int maxdepth)
{
  long *ai = new long[ncoeffs];
  long *bi = new long[ncoeffs];
  fill_all(ai,-1); fill_all(bi,+1);
  ai[1] = 0;               // switch x and -x; this symmetry halves the relevant box
  bi[0] = bi[DEGREE] = 0;  // 3/4 of the half-box is certainly not ND
                           // since first or last coefficient is >=0
  double non, neg;
  // non holds proved non neg def volume proportion
  // neg holds proved neg def volume proportion
  // depth starts negative, each recursion incrememnts it or stops when 0
  QND(-maxdepth, ai, bi, non, neg);
  delete [] ai, bi;
  cout << "\nAfter recursion in the quarter box, non = " << non << ", neg = " << neg << endl;

  double nonND = (3+non)/4;
  double    ND = neg/4;
  cout << ND << " <= (neg.def.density) <= " << 1-nonND << endl;
  cout << "lower bound for non-neg def density  = " << nonND << endl;
  cout << "upper bound for non-neg def density  = " << 1-ND << endl;
  double mid = (1+nonND-ND)/2;
  double err = (1-nonND-ND)/2;
  cout << "middle value for non-neg def density = " << mid << endl;
  cout << "error bound for non-neg def density  = " << err << endl;

  if (DEGREE==2)
    {
      double val =  0.813603354745553;
      cout << "exact value = " << val << "\t";
      if ((nonND<=val) && (val<=1-ND))
        cout << "--OK, in interval";
      else
        cout << "--wrong, not in interval!";
      cout << endl;
    }
}


int main()
{
  pari_init(100000000,2);
  cout << "Density of non-negative definite real polynomials of degree " << DEGREE << endl;
  cout << "Input depth of recursion: ";
  int maxdepth;
  cin >> maxdepth;
  nonNDdensity2(maxdepth);
}
