//Version using integers only, no doubles, and libpari

// -- using simplified neg def criterion, just f(x)<0 for x = 0, 1, -1, infinity

#include <math.h>
#include <iostream>
#include <iomanip>
#include <queue>
using namespace std;

#include <pari/pari.h>

//#define DEBUG

#ifndef DEGREE
//#define DEGREE 10
//#define DEGREE 8
//#define DEGREE 6
#define DEGREE 4
//#define DEGREE 2
#endif
#define ncoeffs (1+DEGREE)

void fill_all(vector<long>& ai, long c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] = c;
}

void scale(vector<long>& ai, long c)
{
  for (int i=0; i<ncoeffs; i++)
    ai[i] *= c;
}

void assign(vector<long>& res, vector<long> ai)
{
  for (int i=0; i<ncoeffs; i++)
    res[i] = ai[i];
}

void interleave(vector<long>& res, vector<long> ai, vector<long> bi)
{
  for (int i=0; i<ncoeffs; i++)   // ai[0], bi[1], ...
    res[i] = (i%2? bi[i] : ai[i]);
}

long evaluate(vector<long> ai, long x)
{
  long res=ai[0];
  for (int i=1; i<ncoeffs; i++)
    res = res*x+ai[i];
  return res;
}

long evaluate2(vector<long> ai, long x, long y)
{
  long res=ai[0]*y + ai[1]*x;
  for (int i=2; i<ncoeffs; i++)
    res = res*y+ai[i]*pow(x,i);
  return res;
}

long volume(vector<long> ai, vector<long> bi)
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

void print_coeffs(vector<long> ai)
{
  for (int i=0; i<ncoeffs; i++)
    {
      if(i) cout<<" ";
      cout<<ai[i];
    }
}

void show_box(vector<long> ai, vector<long> bi)
{
  cout << "ai: "; print_coeffs(ai); cout << endl;
  cout << "bi: "; print_coeffs(bi); cout << endl;
}

// global variables
GEN g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12;
GEN f;
GEN dummy = stoi(0);

long pari_sturm(vector<long> ai, int pos_only=0, int neg_only=0)
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


int is_neg_def(vector<long> ai, int pos_only=0, int neg_only=0, int simple_criterion_only=0)
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

void QND(int depth, vector<long> co1, vector<long> co2, double& non, double& neg, int simple=0)
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

  vector<long> co3(ncoeffs); // used for temporary coeff lists

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

  if (    is_neg_def(co2, /* pos_only */ 1, /* neg_only */ 0, simple)
          &&  is_neg_def(co3, /* pos_only */ 0, /* neg_only */ 1, simple))
    {
#ifdef DEBUG
      cout << "all negative definite" << endl;
#endif
      neg=1.0; return;
    }
#ifdef DEBUG
  cout << "(b)"<<endl;
  show_box(co1,co2);
#endif
    }

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
      non=1.0; return;
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
  vector<long> sco1(ncoeffs); // to store scaled coeff lists
  vector<long> sco2(ncoeffs); // 
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
  double non2, neg2;
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

  non = (non1+non2)/2.0; // average over two equal subvolumes
  neg = (neg1+neg2)/2.0; // average over two equal subvolumes

}

// version using Manjul's scaling trick, only for degree 4 so far

void nonNDdensity_scaled(int maxdepth)
{
  vector<long> ai(ncoeffs);
  vector<long> bi(ncoeffs);

  // Compute 4 4D volumes

  // w[0] fix 0th coeff =-1
  // w[1] fix 1st coeff =-1
  // w[2] fix 2nd coeff =-1
  // w[3] fix 2nd coeff =+1

  // total volume is (2*w[0]+4*w[1]+w[2]+w[3])/5
  double nonND = 0;
  double ND    = 0;
  int i;

  for(i=0; i<4; i++)
    {
      fill_all(ai,-1); fill_all(bi,+1);
      bi[0]=bi[1]=bi[DEGREE]=0;

      if(i==0)
	{
	  bi[0]=-1;
	}
      else
	{
	  if(i==1)
	    {
	      bi[1]=-1;
	    }
	  else
	    {
	      if(i==2)
		{
		  bi[2]=-1;
		}
	      else
		{
		  if(i==3)
		    {
		      ai[2]=+1;
		    }
		}
	    }
	}

      cout<<"sub-box "<<i<<":\n";      show_box(ai,bi);
      //cout<<"--at start of case "<<i<<", total is "<<(nonND+ND+unknown)<<endl;

      // depth starts negative, each recursion increments it or stops when 0
      double non, neg;
      QND(-maxdepth, ai, bi, non, neg, 0);
      cout << "After recursion in sub-box "<<i<<", non = " << non
      	   << ", neg = " << neg << endl;

      if ((i==0)||(i==1))
	{
          ND    += 4*neg;
          nonND += 4*non;
	}
      else
	{
          ND    += neg;
          nonND += non;
	}
    }

  ND = ND/40;
  nonND = (nonND+30)/40;

  cout<<"Total: neg def = "<<ND<<", non = "<<nonND<<endl;

  cout << ND << " <= (neg.def.density) <= " << 1-nonND << endl;
  cout << "lower bound for non-neg def density  = " << nonND << endl;
  cout << "upper bound for non-neg def density  = " << 1-ND << endl;
  double mid = (1+nonND-ND)/2;
  double err = (1-nonND-ND);
  cout << "middle value for non-neg def density = " << mid << endl;
  cout << "interval width for non-neg def density  = " << err << endl;
}

int QND1(queue<pair<vector<long>,vector<long> > >& bq, double& non, double& neg)
{
  pair<vector<long>,vector<long> > co1co2 = bq.front(); bq.pop();
  vector<long> co1 = co1co2.first;
  vector<long> co2 = co1co2.second;
  double v = volume(co1,co2); // volume of popped box
  long s = 0; // scaling factor for the box
  if (co1[0]==co2[0])
    {
      s = co1[0];
    }
  else
    {
      if (co1[1]==co2[1])
        {
          s = co1[1];
        }
      else
        {
          s = co1[2];
          v/=2;
        }
    }
  v /= (s*s*s*s);

  vector<long> co3(ncoeffs); // used for temporary coeff lists

  interleave(co3, co2, co1);         // co2[0], co1[1], co2[2], ...

  // (1) the whole box is neg def iff
  //
  // ((co2(x)<0 for all x>0) AND (co3(x)<0 for all x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies f(x) < co3(x)

  if (    is_neg_def(co2, /* pos_only */ 1, /* neg_only */ 0, 0)
          &&  is_neg_def(co3, /* pos_only */ 0, /* neg_only */ 1, 0))
    {
      //cout<<"Adding "<<v<<" to neg from box "<<endl;
      //show_box(co1,co2);
      neg+=v; return 1;
    }

  interleave(co3, co1, co2);   // co1[0], co2[1], co1[2], ...

  // (2) the whole box is NOT neg def if (but NB not only if)
  //
  // ((co1(x)>0 for some x>0) OR (co3(x)>0 for some x<0))
  //
  // since for f in the box,
  // x>0 => co1(x) < f(x) < co2(x) and
  // x<0 implies co3(x) < f(x)

  if (   !is_neg_def(co1,  /* pos_only */ 1, /* neg_only */ 0, 0)
         || !is_neg_def(co3,  /* pos_only */ 0, /* neg_only */ 1, 0))
    {
      //cout<<"Adding "<<v<<" to non from box "<<endl;
      //show_box(co1,co2);
      non+=v; return 1;
    }

  // (3) Now this box is not all in and possibly not all out.  We form
  // two smaller boxes (dividing a longest dimension by 2) and add
  // them to the queue.  To keep integer coefficients we double all
  // coordinates if necessary, which does not affect the densities.

  int j=0; // index of longest box edge
  long w; // holds length of longest box edge
  long w2;
  // initialise:
  w=co2[0]-co1[0];
  // look for a longer edge:
  for (int i=1; i<ncoeffs; i++)
    {
      w2=co2[i]-co1[i];
      if (w2>w) // i'th dimension is greater, so update
        {
          w=w2;
          j=i;
        }
    }

  long f=co1[j]+co2[j];
  // double both co1, co2 unless f is even:
  vector<long> sco1(ncoeffs); // to store scaled coeff lists
  vector<long> sco2(ncoeffs); // 
  assign(sco1, co1);
  assign(sco2, co2);
  if (f%2) // f is odd
    {
      scale(sco1,2);
      scale(sco2,2);
    }
  else // f is even
    {
      f /= 2;
    }
  // so now f == (co1[j]+co2[j])/2 and is integral in both cases

  // first sub-box: co3 is the same as co2 except for the j'th entry which is the mean
  assign(co3, sco2);
  co3[j] = f;
  bq.push(pair<vector<long>,vector<long> > (sco1,co3));

  // second sub-box: co3 is the same as co1 except for the j'th entry which is the mean
  assign(co3, sco1);
  co3[j] = f;
  bq.push(pair<vector<long>,vector<long> > (co3,sco2));

  return 0;
}

queue<pair<vector<long>,vector<long> > > box_queue;

void nonNDdensity_inc(int maxsteps=1000)
{
  // Compute 4 4D volumes

  double nonND = 30.0;
  double ND    = 0.0;
  int i;
  vector<long> a(ncoeffs);
  vector<long> b(ncoeffs);

  fill_all(a,-1); fill_all(b,+1);

  for(i=0; i<4; i++)
    {
      vector<long> ai = a;
      vector<long> bi = b;
      bi[0] = bi[1] = bi[DEGREE]=0;
      if(i<3)
        bi[i]=-1;
      else
        ai[2]=+1;
      box_queue.push(pair<vector<long>,vector<long> > (ai,bi));
    }

  i=0;
  int change;
  while (!box_queue.empty()) // which will never happen
    {
      i +=1;
      change = QND1(box_queue, nonND, ND);
      if(change) cout << i << "/"<<box_queue.size()<<": \t"
                      << setw(10) << (nonND/40) << " < non-neg-def density < \t" << (1-ND/40) << endl;
      if (maxsteps && (i>=maxsteps)) break;
    }

  nonND = nonND/40;
  ND    = ND/40;

  cout<<"Total after scaling: neg def = "<<ND<<", non = "<<nonND<<endl;

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
  cout << "Density of non-negative definite real polynomials of degree " << DEGREE << endl;
  int depth, simple=1;
  cout << "\nScaled incremental version" << endl;
  cout << "Depth-first recursive version? "; cin>>depth;
  if (depth)
    {
      cout << "Input depth of recursion: ";
      cin >> depth;
      nonNDdensity_scaled(depth);
    }
  else
    {
      cout << "Starting breadth-first version" << endl;
      cout << "Input number of steps (0 for no limit): ";
      cin >> depth;
      nonNDdensity_inc(depth);
    }
}
