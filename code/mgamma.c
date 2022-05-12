#include <stdlib.h>
#include <stdio.h>
#include <string.h> // for memcpy
#include "mgamma.h"

// function print_int_array(): utility for debugging

void  print_int_array(int *v, int n)
{
  printf("[");
  int i;
  for (i=0; i<n; i++)
    {
      if (i)
        printf(",");
      printf("%d", v[i]);
    }
  printf("]");
}

// function poly_div_rem()

// p is an odd prime

// fc is an array of length at least n+1 holding the coefficients
// of a monic degree n polynomial, with fc[i] the coefficient of x^i
// and fc[n]=1.

// c is an integer

// The returned value is f(c), and on return, the first n entries of
// fc hold the coefficients of g(x) such that f(x)=(x-c)g(x) + f(c).

int poly_div_rem(int n, int p, int *fc, int c)
{
  register int j, t, u;
  t = 1;
  for ( j=n-1; j>=0; j--)
    {
      u = t;
      t *= c;
      t += fc[j];
      t %= p;
      fc[j] = u;
    }
  return t;
}

// function signed_root_multiplicity() ////////////////////////////////////////

// p is an odd prime

// legendre is an array of length p with legendre[i] = legendre_symbol(i,p)

// fc is an array of length at least n+1 holding the coefficients
// of a monic degree n polynomial, with fc[i] the coefficient of x^i
// and fc[n]=1.

// c is an integer

// The returned value is +m or -m or 0 where f(x)=(x-c)^m * g(x) with
// g(x) nonzero. If m is nonzero and even, the sign is the legendre
// symbol of g(c). If m is nonzero and odd, the sign is +1.


int signed_root_multiplicity(int n, int p, int *legendre, int *fc, int c)
{
  // we take a copy of the coefficient array since poly_div_rem() overwrites it

  int *gc = (int*)malloc(n * sizeof(int));
  memcpy(gc, fc, n*sizeof(int));

  register int v, d=n, m=0;
  v = poly_div_rem(d, p, gc, c);
  while (v==0)
    {
      d--; m++;
      v = poly_div_rem(d, p, gc, c);
    }
  free(gc);
  if (m%2==0)
    m *= legendre[v];
  return m;
}


// function root_multiplicities() //////////////////////////////////////////

// p is an odd prime

// legendre is an array of length p with legendre[i] = legendre_symbol(i,p)

// fc is a const array of length n+1 holding the coefficients of a
// monic degree n polynomial, with fc[i] the coefficient of x^i and
// fc[n]=1.

// rts is an array of length p.

// On input rts[i] = 1 if i is a root of f mod p, else 0.

// On return, rts[i] = +m>0 or -m<0, if i is a root of signed
// multiplicity m, + or m,-; else 0.

void root_multiplicities(int n, int p, int *legendre, int *fc, int *rts)
{
  /* printf("root_multiplicities of "); */
  /* print_int_array(fc, n+1); */
  /* printf(" with root flags "); */
  /* print_int_array(rts, p); */
  /* printf("\n"); */

  register int i;
  for(i=0; i<p; i++)
    {
      if (rts[i])
        rts[i] = signed_root_multiplicity(n, p, legendre, fc, i);
    }
  /* printf(" -- root multiplicities "); */
  /* print_int_array(rts, p); */
  /* printf("\n"); */
}

int cmp (const void * a, const void * b) {
  return ( *(int*)a - *(int*)b );
}

void sort(int n, int *rts)
{
  qsort(rts, n, sizeof(int), cmp);
}


// Convert an array of ints to a string: sorted then 0s removed and with leading signs.
// NB this function creates the string using malloc

char* encode(int n, int *rts)
{
  register int i, pos, m, k;
  char *code = (char*)malloc(n * 5 * sizeof(int)); // allow space+sign+2 digits
  pos = sprintf(code, "%s", "[");
  for (i=0, m=0; i<n; i++)
    {
      if (rts[i])
        {
          m++;
          pos += sprintf(code+pos, "%+d,", rts[i]);
        }
    }
  if (m)
    code[strlen(code)-1] = ']'; // change last character from ',' to ']'
  else
    pos += sprintf(code+pos, "%s", "]");
  return code;
}

// find code in a list of strings, return index if it is there, else -1

int find_code(char* code, char** codes, int ncodes)
{
  register int i;
  for (i=0; i<ncodes; i++)
    if (strcmp(code, codes[i])==0)
      return i;
  return -1;
}

// Compute root multiplicities, sort and encode:

char* root_multiplicity_code(int n, int p, int *legendre, int *fc, int *rts)
{
  int i;
  root_multiplicities(n, p, legendre, fc, rts);
  sort(p, rts);
  return encode(p, rts);
}

// Compute root multiplicities, sort and encode, returning both the code and the flipped code:

char** root_multiplicity_codes(int n, int p, int *legendre, int *fc, int *rts)
{
  char **codes = malloc(2*sizeof(char*));
  root_multiplicities(n, p, legendre, fc, rts);
  sort(p, rts);
  codes[0] = encode(p, rts);
  flip_multiplicities(p, rts);
  sort(p, rts);
  codes[1] = encode(p, rts);
  return codes;
}

// given an array of signed multiplicities, change the sign of the even ones:

void flip_multiplicities(int p, int *mults)
{
  int i, m;
  for (i=0; i<p; i++)
    {
      m = mults[i];
      if (m%2==0)
        mults[i] = -m;
    }
}


// Flip signs in a code (+ to - and vice versa)

// First make a copy.  Find all '+' in the original and change to '-'
// in the copy, then find all '-' in the original and change to '+' in
// the copy.

char* flip_signs(char* code)
{
  int n = strlen(code);
  char *ucode = (char*)malloc(n);
  memcpy(ucode, code, n);
  if (n==0)
    return ucode;
  /* printf("flipping signs in code %s...\n", code); */
  char *pos = strchr(code, '+');
  while (pos)
    {
      ucode[pos-code] = '-';
      pos = strchr(pos+1, '+');
    }
  pos = strchr(code, '-');
  while (pos)
    {
      ucode[pos-code] = '+';
      pos = strchr(pos+1, '-');
    }
  /* printf("after flipping signs, code is %s...\n", ucode); */
  return ucode;
}
