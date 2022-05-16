#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>
#include "mgamma.h"

#define DEG    6
#define MAXP    128
#define NCODES  100

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    long xnptless1, xnptless2; // 1 is #orbits, 2 is total: y^2=f(x)
    long xnptless1u, xnptless2u; // 1 is #orbits, 2 is total: uy^2=f(x)
    int DEG1=DEG-1, DEG2=DEG-2, DEG3=DEG-3, DEG4=DEG-4;
    int qmap[MAXP*MAXP];
    int legendre[MAXP];
    int xmap[DEG*MAXP];
    char* codes_1[NCODES];
    char* codes_u[NCODES];
    long code_counts_1[NCODES];
    long code_counts_u[NCODES];
    int ncodes_1 = 0;
    int ncodes_u = 0;
    int i, j, p, pm1;
    int u; // will hold the least quadratic nonresidue
    int output_polynomials = 0;

    if ( argc < 2 ) { printf ("mgamma%d p (or mgamma%d p 1)\n", DEG, DEG); return 0; }
    p = atoi(argv[1]);
    if ( p < 3 || p > MAXP ) { printf ("p must be in [3,%d]\n", MAXP); return 0; }
    if (argc > 2) output_polynomials = atoi(argv[2]);

    start = omp_get_wtime();

    pm1 = p-1; // size of orbits under affine transformations unless f[DEG1]==0

    // set qmap[i] = 1 + kron(i,p) for i in [0,p^2]
    memset(qmap,0,sizeof(qmap));
    qmap[0] = 1;
    for ( i = 1 ; i < p ; i++ )
      qmap[zmod(i*i,p)] = 2;
    for ( i = 0 ; i < p ; i++ )
      for ( j = 1 ; j < p ; j++ )
        qmap[j*p+i] = qmap[i];
    for ( i = 1 ; i < p ; i++ )
      legendre[i] = qmap[i]-1;

    // Find the least nonresidue
    u = 2;
    while ( qmap[u] ) u++;

    // set xmap[DEG*i+j] = i^(j+1) mod p for i in [0,p-1] and j in [1,DEG]
    for ( i = 0 ; i < p ; i++ )
      {
        xmap[DEG*i] = i;
        for ( j = 1 ; j <= DEG ; j++ )
          xmap[DEG*i+j] = zmod(i*xmap[DEG*i+j-1],p);
      }

    xnptless1 = xnptless2 = 0;
    xnptless1u = xnptless2u = 0;
#pragma omp parallel num_threads(p)
    {
      int f[DEG+1]; // coeffs of f
      int df[DEG];  // coeffs of f'
      register int i, ny, cnt, ucnt, f_mult,
          *x;
        char **codes;
        int emap[MAXP], edmap[MAXP], rts[MAXP];

        f[DEG] = 1;
        df[DEG1] = DEG;
        f[DEG2] = omp_get_thread_num();
        df[DEG3] = zmod((DEG2)*f[DEG2], p);
        for ( f[DEG1] = 0 ; f[DEG1] < 2 ; f[DEG1]++ ) {
        f_mult = (f[DEG1]==0? 1: pm1);
        df[DEG2] = zmod((DEG1)*f[DEG1], p);
        //
        // for k=DEG-3, DEG-4, down to 2, (DEG-4 loops) include lines
        //
        // for ( f[k] = 0 ; f[k] < p ; f[k]++ ) { df[k-1] = zmod(k*f[k], p);
        //
        for ( f[3] = 0 ; f[3] < p ; f[3]++ ) { df[2] = zmod(3*f[3], p);
        for ( f[2] = 0 ; f[2] < p ; f[2]++ ) { df[1] = zmod(2*f[2], p);

          // set emap[i] = f(i)-f[1]*i-f[0] for i in [0,p-1]
          // and edmap[i] = f'(i)-f[1]
          for ( i = 0 ; i < p ; i++ ) {
                x = xmap + i*DEG - 1;  // x[j] = i^j
                // RHS is x[DEG] + sum(f[k]*x[k] for k in 2..DEG1)
                emap[i] = zmod(f_eval(DEG, f, x, 2), p);
                // RHS is DEG*x[DEG1] + sum(df[k]*x[k] for k in 1..DEG2)
                edmap[i] = zmod(f_eval(DEG1, df, x, 1), p);
            }
          // inner loop over lowest two coefficients, f[1] and f[0]:
          for ( f[1] = 0 ; f[1] < p ; f[1]++ ) {
            for ( f[0] = 0 ; f[0] < p ; f[0]++ ) {
              for ( cnt = 0, ucnt = 0, i = 0 ; i < p && (cnt==0 || ucnt==0); i++ )
                      {
                        ny = qmap[emap[i]+f[1]*i+f[0]]; // # of y with y^2=f(i)
                        rts[i] = (ny==1); // flags if i is a root
                        // if ny==1 we have a zero and need to check that it is not a double zero
                        if (ny != 1 || zmod(edmap[i]+f[1],p) != 0)
                          {
                            cnt += ny;
                            ucnt += 2-ny;
                          }
                      }
                    if ( cnt == 0 || ucnt == 0)
#pragma omp critical(min)
                      { // critical block, can only be executed by one thread at a time
                        codes = root_multiplicity_codes(DEG, p, legendre, f, rts);
                        if (cnt==0)
                          {
                            xnptless1 ++;
                            xnptless2 += f_mult;
                            update_code_counts(codes[0], codes_1, &ncodes_1, code_counts_1, f_mult);
                            if (ncodes_1>NCODES)
                              {
                                printf("*** error:  NCODES value %d is too small!\n", NCODES);
                                exit(1);
                              }
                            if (output_polynomials)
                              {
                                printf ("%d 1 [1", p);
                                for(i=DEG1; i>=0; i--)
                                  printf(",%d", f[i]);
                                printf("] %s %d\n", codes[0], f_mult);
                              }
                          }
                        if ((ucnt==0) && (!is_square(DEG, f, p)))
                          {
                            xnptless1u ++;
                            xnptless2u += f_mult;
                            update_code_counts(codes[1], codes_u, &ncodes_u, code_counts_u, f_mult);
                            if (ncodes_u>NCODES)
                              {
                                printf("*** error:  NCODES value %d is too small!\n", NCODES);
                                exit(1);
                              }
                            if (output_polynomials)
                              {
                                printf ("%d u [1", p);
                                for(i=DEG1; i>=0; i--)
                                  printf(",%d", f[i]);
                                printf("] %s %d\n", codes[1], f_mult);
                              }
                          }
                      } // end of critical block
                } // end of f[0] loop
          }     // end of f[1] loop
          // next line has DEG3 * } ending f[k] loops for k=2..DEG2 (DEG1 is thread number)
        }}}
    } // end of parallel block

    printf ("Checked %ld curves in %.3fs\n", 3*(long)pow(p,DEG2), omp_get_wtime()-start);
    printf ("#Gamma(%d,1) =  %ld (in %ld orbits) for p = %d\n", DEG, xnptless2, xnptless1, p);
    printf ("#Gamma(%d,u) =  %ld (in %ld orbits) for p = %d\n", DEG, xnptless2u, xnptless1u, p);
    printf ("\n");
    printf ("Frequencies of signed root multiplicities\n");
    printf ("Gamma(%d,1): %d different patterns\n", DEG, ncodes_1);
    for (i=0; i<ncodes_1; i++)
      {
        printf("1 %s %ld\n", codes_1[i], code_counts_1[i]);
      }
    printf ("Gamma(%d,u): %d different patterns\n", DEG, ncodes_u);
    for (i=0; i<ncodes_u; i++)
      {
        printf("u %s %ld\n", codes_u[i], code_counts_u[i]);
      }
}
