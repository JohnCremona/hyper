//Version using integers only, no doubles, and libpari

#include <math.h>
#include <iostream>
#include <map>
#include <array>

using namespace std;

#include <eclib/bigrat.h>
const bigrational one(1);
const bigrational two(2);
const bigrational three(3);
const bigrational four(4);
#define maxprime PARImaxprime
#define primes PARIprimes
#include <pari/pari.h>

//#define DEBUG
//#define DEBUG_CACHE
//#define USE_CACHE
//#define TRAIN # turn on one trick for ND quartics

#ifndef DEGREE
//#define DEGREE 10
//#define DEGREE 8
//#define DEGREE 6
#define DEGREE 4
//#define DEGREE 2
#endif
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

long evaluate2(long *ai, long x, long y)
{
  long res=ai[0]*y + ai[1]*x;
  for (int i=2; i<ncoeffs; i++)
    res = res*y+ai[i]*pow(x,i);
  return res;
}

long volume(long* ai, long* bi)
{
  long v=1;
  for (int i=0; i<ncoeffs; i++)
    {
      long d = (bi[i] - ai[i]);
      // we use this function for degenerae boxes too, where the
      // dimension is smaller but we still want a positive volume!
      if (d>0) v *= d;
    }
  return v;
}

// Quartic invariants and covariants and pos/neg def test

long i4(long a, long b, long c, long d, long e)
{
  return 12*a*e-3*b*d+c*c;
}

long j4(long a, long b, long c, long d, long e)
{
  return 72*a*c*e+9*b*c*d-27*a*d*d-27*e*b*b-2*c*c*c;
}

long h4(long a, long b, long c)
{
  return 8*a*c-3*b*b;
}

long q4(long a, long b, long c, long d, long e)
{
  return 3*b*b*b*b + 16*(a*a*(c*c+b*d)-a*b*b*c) - 64*a*a*a*e;
}

long disc4(long a, long b, long c, long d, long e)
{
  long i = i4(a,b,c,d,e);
  long j = j4(a,b,c,d,e);
  return 4*i*i*i-j*j;
}

int is_quartic_neg_def(long a, long b, long c, long d, long e)
{
  if ((a>=0) || (e>=0) || ((a+b+c+d+e)>=0) or ((a-b+c-d+e)>=0))
    {return 0;}
  if (disc4(a,b,c,d,e) <= 0)
    {return 0;}
  // now D>0, we require H>0 or Q<0
  // (since a<0 it cannot be pos def)
  return (h4(a,b,c) >= 0) || (q4(a,b,c,d,e) <= 0);
}

long i4(long* ai) {return i4(ai[0],ai[1],ai[2],ai[3],ai[4]);}
long j4(long* ai) {return j4(ai[0],ai[1],ai[2],ai[3],ai[4]);}
long h4(long* ai) {return h4(ai[0],ai[1],ai[2]);}
long q4(long* ai) {return q4(ai[0],ai[1],ai[2],ai[3],ai[4]);}
long disc4(long* ai) {return disc4(ai[0],ai[1],ai[2],ai[3],ai[4]);}
long is_quartic_neg_def(long* ai) {return is_quartic_neg_def(ai[0],ai[1],ai[2],ai[3],ai[4]);}

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
  // Only for degrees 2, 4, 6, 8, 10 so far, since mkpoln needs all the coeffs individually.
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
    res = sturmpart(f,gen_0,NULL); // #roots >=0
  else
    {
      if (neg_only)
        res = sturmpart(f,NULL,gen_0); // #roots <=0
      else
        res = sturm(f);                  // #roots
    }
  gerepileupto(av, dummy);
  return res;
}

// global caches for results of the is_neg_def() function:

typedef array<long,ncoeffs> poly;
typedef map<poly,int> poly_cache;

poly make_poly(long* ai)
{
  poly f;
  for (int i=0; i<ncoeffs; i++)
    f[i] = ai[i];
  return f;
}

void print_poly(poly f)
{
  for (int i=0; i<ncoeffs; i++)
    {
      if(i) cout<<" ";
      cout<<f[i];
    }
}

void print_cache(poly_cache cache)
{
  poly_cache::const_iterator res = cache.begin();
  while (res!=cache.end())
    {
      print_poly(res->first);
      cout << " ---> " << res->second << endl;
      res++;
    }
}

poly_cache ND_cache_all, ND_cache_pos, ND_cache_neg;

int is_neg_def_uncached(long* ai, int pos_only=0, int neg_only=0, int simple_criterion_only=0);
int is_neg_def_cached(long* ai, int pos_only=0, int neg_only=0, int simple_criterion_only=0);
int is_neg_def(long* ai, int pos_only=0, int neg_only=0, int simple_criterion_only=0);

int is_neg_def_cached(long* ai, int pos_only, int neg_only, int simple_criterion_only)
// Return 1 iff the poly with coeffs ai is negative definite, by default for
// all x in R; if pos_only==1 then test only for x>=0, and if
// neg_only=1 then test only for x<=0.  Use global cache, getting the
// result from the generic code, and storing in the cache, if it's new.
{
  poly_cache& cache = (pos_only? ND_cache_pos : (neg_only? ND_cache_neg: ND_cache_all));
  int v;
  poly f = make_poly(ai);
  poly_cache::const_iterator res = cache.find(f);
  if (res==cache.end())
    {
      v = is_neg_def_uncached(ai, pos_only, neg_only);
      cache[f] = v;
#ifdef DEBUG_CACHE
      cout<<"Caching value " << v << " for poly ";
      print_coeffs(ai);
      cout<<endl;
#endif
    }
  else
    {
      v = res->second;
#ifdef DEBUG_CACHE
      cout<<"Found cached value " << v << " for poly ";
      print_coeffs(ai);
      cout<<endl;
#endif
    }
#ifdef DEBUG_CACHE
  print_cache(cache);
#endif
  return v;
}

int is_neg_def_uncached(long* ai, int pos_only, int neg_only, int simple_criterion_only)
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
  if ((DEGREE==4) && (pos_only==0) && (neg_only==0))
    return is_quartic_neg_def(ai);

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

  if(!neg_only)
    if (evaluate(ai,2)>=0) return 0;
  if(!pos_only)
    if (evaluate(ai,-2)>=0) return 0;
  if(!neg_only)
    if (evaluate2(ai,2,1)>=0) return 0;
  if(!pos_only)
    if (evaluate2(ai,-2,1)>=0) return 0;

  if (simple_criterion_only) return 1;

  // now the leading coeff is negative so f(x) is neg def if it has no real roots:

  return pari_sturm(ai, pos_only, neg_only)==0;
}
#endif

int is_neg_def(long* ai, int pos_only, int neg_only, int simple_criterion_only)
{
#ifdef USE_CACHE
  return is_neg_def_cached(ai, pos_only, neg_only);
#else
  return is_neg_def_uncached(ai, pos_only, neg_only);
#endif
}

void QND(int depth, long *co1, long *co2, bigrational& non, bigrational& neg, int simple=0)
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

  if (!simple)
    {
  // (1) the whole box is neg def iff
  //
  // ((co2(x)<0 for all x>0) AND (co3(x)<0 for all x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies f(x) < co3(x)
  //
  // Equivalently, iff co2 and co3 are both neg def, which is faster to check

  if (    is_neg_def(co2, /* pos_only */ 0, /* neg_only */ 0, simple)
          &&  is_neg_def(co3, /* pos_only */ 0, /* neg_only */ 0, simple))
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
    }

#ifdef TRAIN
  // New condition:  if all (a,b,c,d,e) in the box satisfy
  // (i)   a<0
  // (ii)  e<0
  // (iii) c>0
  // (iv)  c^2>4ae
  //
  // then there exists y=-c/2a>0 such that g(y)=ay^2+cy+e>0 so there
  // exists x such that f(x)+f(-x)=2g(x^2)>0, so f is not ND.

  // This will hold for all f in the box if
  // co2[0]<=0, co2[4]<=0
  // co1[2]>=0
  // co1[2]^2 >= co1[0]*co1[4]


  if ((co2[0]<=0) && (co2[4]<=0) && (co1[2]>=0) && (co1[2]*co1[2]>=4*co1[0]*co1[4]))
    {
#ifdef DEBUG
      cout << "none negative definite (new condition)" << endl;
#endif
      non=1.0; return;
    }
#endif // TRAIN

  interleave(co3, co1, co2);   // co1[0], co2[1], co1[2], ...
#ifdef DEBUG
  cout << "(c)"<<endl;
  show_box(co1,co2);
#endif

  // (2) the whole box is NOT neg def if (but NB not only if)
  //
  // ((co1(x)>0 for some x>0) OR (co3(x)>0 for some x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies co3(x) < f(x)

  if (   !is_neg_def(co1,  /* pos_only */ 1, /* neg_only */ 0, simple)
         || !is_neg_def(co3,  /* pos_only */ 0, /* neg_only */ 1, simple))
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

  // (3) Now this box is not all in and possibly not all out. If the maximum
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

#ifdef TRAIN
  // Nov 2019: split on coeff of x^4 or x^2 or x^0 if the range
  // includes both positive and negative
  if ((co2[0]>0) && (0>co1[0]))
    {
      j=0;
    }
  else if ((co2[2]>0) && (0>co1[2]))
    {
      j=2;
    }
  else if ((co2[4]>0) && (0>co1[4]))
    {
      j=4;
    }
  else
#endif // TRAIN
    {
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
  bigrational non1, neg1;
  QND(depth+1, sco1, co3, non1, neg1, simple);
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
  bigrational non2, neg2;
  QND(depth+1, co3, sco2, non2, neg2, simple);
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

  non = (non1+non2)/two; // average over two equal subvolumes
  neg = (neg1+neg2)/two; // average over two equal subvolumes

  delete[] co3;
  delete[] sco1;
  delete[] sco2;
}

void nonNDdensity2(int maxdepth, int simple=0)
{
  long *ai = new long[ncoeffs];
  long *bi = new long[ncoeffs];
  fill_all(ai,-1); fill_all(bi,+1);
  ai[1] = 0;               // switch x and -x; this symmetry halves the relevant box
  bi[0] = bi[DEGREE] = 0;  // 3/4 of the half-box is certainly not ND
                           // since first or last coefficient is >=0
  bigrational non, neg;
  // non holds proved non neg def volume proportion
  // neg holds proved neg def volume proportion
  // depth starts negative, each recursion incrememnts it or stops when 0
  QND(-maxdepth, ai, bi, non, neg, simple);
  delete [] ai, bi;
  if (!simple)
    {
      cout << "\nAfter recursion in the quarter box, non = " << non << ", neg = " << neg << endl;
    }
  bigrational nonND = (three+non)/four, ND = neg/four;
  if (!simple)
    {
      cout << ND << " <= (neg.def.density) <= " << one-nonND << endl;
    }
  cout << "lower bound for non-neg def density  = " << nonND << endl;
  if (!simple)
    {
      cout << "upper bound for non-neg def density  = " << one-ND << endl;
      bigrational mid = (one+nonND-ND)/two;
      bigrational err = (one-nonND-ND)/two;
      cout << "middle value for non-neg def density = " << mid << endl;
      cout << "error bound for non-neg def density  = " << err << endl;
    }
  if (DEGREE==2)
    {
      double val =  0.813603354745553;
      cout << "exact value = " << val << "\t";
      if ((bigfloat(nonND)<=val) && (val<=1-bigfloat(ND)))
        cout << "--OK, in interval";
      else
        cout << "--wrong, not in interval!";
      cout << endl;
    }
}

// version using Manjul's scaling trick, only for degree 4 so far

void nonNDdensity_scaled(int maxdepth)
{
  long *ai = new long[ncoeffs];
  long *bi = new long[ncoeffs];

  // Compute 4D volumes

  bigrational nonND = bigrational(6*(DEGREE+1));
  bigrational ND    = bigrational(0);
  bigrational non, neg, fac;
  int i, r;

  for(i=0; i<DEGREE; i++)
    {
      fill_all(ai,-1); fill_all(bi,+1);
      bi[DEGREE]=0;
      bi[0]=0;
      bi[1]=0;
      if(i<2)
	{
	  ai[i]=bi[i]=-1;
	}
      else
        {
          r = 1+(i>>1);
          ai[r]=bi[r]=(i&1?-1:+1);
        }

      // depth starts negative, each recursion increments it or stops when 0
      QND(-maxdepth, ai, bi, non, neg, 0);
      fac = 2;
      if (i<2) fac = 4;
      if (i>(DEGREE-3)) fac = 1;
      nonND   += fac*non;
      ND      += fac*neg;
    }

  nonND = nonND / bigrational(8*(DEGREE+1));
  ND    = ND / bigrational(8*(DEGREE+1));

  cout<<"Total after scaling: neg def = "<<ND<<", non = "<<nonND<<endl;

  cout << ND << " <= (neg.def.density) <= " << one-nonND << endl;
  cout << "lower bound for non-neg def density  = " << nonND << " = " << bigfloat(nonND) << endl;
  cout << "upper bound for non-neg def density  = " << one-ND << " = " << 1-bigfloat(ND) << endl;
  bigrational mid = (one+nonND-ND)/two;
  bigrational err = (one-nonND-ND)/two;
  cout << "middle value for non-neg def density = " << mid << " = " << bigfloat(mid) << endl;
  cout << "error bound for non-neg def density  = " << err << " = " << bigfloat(err) << endl;
  delete [] ai, bi;
}


int main()
{
  pari_init(100000000,2);
  std::cout.precision(10);
  cout << "Density of non-negative definite real polynomials of degree " << DEGREE << endl;
  int maxdepth, simple=0;
  //  cout << "Use full (0) or simplified (1) criterion? ";
  //  cin >> simple;
  cout << "Input depth of recursion: ";
  cin >> maxdepth;
  int scaled=1;
  cout << "Use old (0) or new scaled (1) version? ";
  cin >> scaled;
  if (scaled)
    {
      cout << "\nScaled version, depth = " << maxdepth << endl;
      nonNDdensity_scaled(maxdepth);
    }
  else
    {
      cout << "\nUnscaled version, depth = " << maxdepth << endl;
      nonNDdensity2(maxdepth, simple);
    }
}
