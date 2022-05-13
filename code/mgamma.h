// function print_int_array(): utility for debugging

void  print_int_array(int *v, int n);

// function poly_div_rem() ///////////////////////////////////////////////////////

// p is an odd prime

// fc is an array of length at least n+1 holding the coefficients
// of a monic degree n polynomial, with fc[i] the coefficient of x^i
// and fc[n]=1.

// c is an integer

// The returned value is f(c), and on return, the first n entries of
// fc hold the coefficients of g(x) such that f(x)=(x-c)g(x) + f(c).

int poly_div_rem(int n, int p, int *fc, int c);

// function signed_root_multiplicity() ////////////////////////////////////////

// p is an odd prime

// legendre is an array of length p with legendre[i] = legendre_symbol(i,p)

// fc is an array of length at least n+1 holding the coefficients
// of a monic degree n polynomial, with fc[i] the coefficient of x^i
// and fc[n]=1.

// c is an integer

// The returned value is +m or -m or 0 where f(x)=(x-c)^m * g(x) with
// g(x) nonzero and the sign (if m is nonzero) is the legendre symbol
// of g(c).


int signed_root_multiplicity(int n, int p, int *legendre, int *fc, int c);


// function root_multiplicities() /////////////////////////////////////////////

// p is an odd prime

// legendre is an array of length p with legendre[i] = legendre_symbol(i,p)

// fc is a const array of length n+1 holding the coefficients of a
// monic degree n polynomial, with fc[i] the coefficient of x^i and
// fc[n]=1.

// rts is an array of length p.

// On input rts[i] = 1 if i is a root of f mod p, else 0.

// On return, rts[i] = +m>0 or -m<0, if i is a root of signed
// multiplicity m, + or m,-; else 0.

void root_multiplicities(int n, int p, int *legendre, int *fc, int *rts);

// given an array of signed multiplicities, change the sign of the even ones:

void flip_multiplicities(int p, int *mults);

// sort an array of ints:

void sort(int n, int *rts);

// Convert an array of ints to a string: sorted then 0s removed and with leading signs.
// NB this function creates the string using malloc

char* encode(int n, int *rts);

// find code in a list of strings, return index if it is there, else -1

int find_code(char* code, char** codes, int ncodes);

// Compute root multiplicities, sort and encode:

char* root_multiplicity_code(int n, int p, int *legendre, int *fc, int *rts);

// Compute root multiplicities, sort and encode, returning both the code and the flipped code:

char** root_multiplicity_codes(int n, int p, int *legendre, int *fc, int *rts);

// Flip signs in a code (+ to - and vice versa)

char* flip_signs(char* code);

// update code multiplicity counts: look up code in the list of codes,
// if is has index i then increment the i'th counter by mult,
// otherwise add it to the list, increment ncodes and set the i'th
// counter to mult.

void update_code_counts(char *code, char **codes, int *ncodes, long *code_counts, int mult);

// Functions to test whether monic polys mod p are squares.  Here f is
// an array of length n+1 with f[n]=1.

int is_square(int n, int* f, int p);
