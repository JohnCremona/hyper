#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>
#include "mgamma.h"

#define MAXD    8
#define MAXP    128
#define NCODES  100

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    long xnptless1, xnptless2; // 1 is #orbits, 2 is total: y^2=f(x)
    long xnptless1u, xnptless2u; // 1 is #orbits, 2 is total: uy^2=f(x)
    int orbit_size, p2, half;
    int qmap[MAXP*MAXP];
    int legendre[MAXP];
    int xmap[MAXD*MAXP];
    char* codes_1[NCODES];
    char* codes_u[NCODES];
    long code_counts_1[NCODES];
    long code_counts_u[NCODES];
    int ncodes_1 = 0;
    int ncodes_u = 0;
    int i, j, p;
    int u; // will hold the least quadratic nonresidue
    int output_polynomials = 0;

    if ( argc < 2 ) { puts ("gamma8 p"); return 0; }
    p = atoi(argv[1]);
    if ( p <= 2 || p > MAXP ) { printf ("p must be in [3,%d]\n", MAXP); return 0; }
    if (argc > 2) output_polynomials = atoi(argv[2]);

    start = omp_get_wtime();

    p2 = p*(p-1)/2; // size of orbits under affine transformations unless f[6]==0
    half = (p+1)/2;

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

    // set xmap[MAXD*i+j] = i^(j+1) mod p for i in [0,p-1] and j in [1,MAXD]
    for ( i = 0 ; i < p ; i++ )
      {
        xmap[MAXD*i] = i;
        for ( j = 1 ; j <= MAXD ; j++ )
          xmap[MAXD*i+j] = zmod(i*xmap[MAXD*i+j-1],p);
      }

    xnptless1 = xnptless2 = 0;
    xnptless1u = xnptless2u = 0;
#pragma omp parallel num_threads(p)
    {
      int f[MAXD+1];
        register int df5, df4, df3, df2, df1,
          h0, h1, h2, // potential coeffs of sqrt(f)
          h1h1, f3s, f2s, f1s, f0s,
          i, ny, cnt, ucnt, f_mult,
          *x;
        char **codes;
        int keep_code, keep_ucode;
        int emap[MAXP], edmap[MAXP], rts[MAXP];

        f[8] = 1; f[7] = 0;
        f[5] = omp_get_thread_num();
        df4 = zmod(5*f[5], p);
        h1 = half*f[5];
        h1h1 = zmod(h1*h1, p);
        for ( f[6] = 0 ; f[6] < 3 ; f[6]++ ) {
        if ( f[6] == 2 ) f[6] = u; // f[6] ranges over 0,1,u where u is least non-residue
        f_mult = (f[6]==0? p: p2);
        h2 = half*f[6];
        f3s = zmod(2*h1*h2, p);
        df5 = zmod(6*f[6], p);
        for ( f[4] = 0 ; f[4] < p ; f[4]++ ) {
          df3 = zmod(4*f[4], p);
          h0 = zmod(half*(f[4]-h2*h2),p);
          f0s = zmod(h0*h0,p);
          f1s = zmod(2*h0*h1,p);
          f2s = zmod(2*h0*h2+h1h1,p);
        for ( f[3] = 0 ; f[3] < p ; f[3]++ ) {
          df2 = zmod(3*f[3], p);
        for ( f[2] = 0 ; f[2] < p ; f[2]++ ) {
          df1 = zmod(2*f[2], p);
          // set emap[i] = f(i)-f[1]*i-f[0] for i in [0,p-1]
          // and edmap[i] = f'(i)-f[1]
          for ( i = 0 ; i < p ; i++ ) {
                x = xmap + i*MAXD - 1;  // x[j] = i^j
                emap[i] = zmod(f[2]*x[2]+f[3]*x[3]+f[4]*x[4]+f[5]*x[5]+f[6]*x[6]+x[8],p);
                edmap[i] = zmod(df1*x[1]+df2*x[2]+df3*x[3]+df4*x[4]+df5*x[5]+ 8*x[7],p);
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
                        codes = root_multiplicity_codes(MAXD, p, legendre, f, rts);
                        keep_code = keep_ucode = 0; // only keep it is it is a new one
                        if (cnt==0)
                          {
                            xnptless1 ++;
                            xnptless2 += f_mult;
                            i = find_code(codes[0], codes_1, ncodes_1);
                            if (i==-1)
                              {
                                i = ncodes_1;
                                codes_1[i] = codes[0];
                                keep_code = 1;
                                code_counts_1[i] = 0;
                                ncodes_1 ++;
                              }
                            code_counts_1[i] += f_mult;
                            if (output_polynomials)
                              {
                                printf ("%d 1 ", p);
                                printf ("[1,0,%d,%d,%d,%d,%d,%d,%d] ", f[6],f[5],f[4],f[3],f[2],f[1],f[0]);
                                printf("%s ", codes[0]);
                                printf("%d ", f_mult);
                                printf("\n");
                              }
                          }
                        if (ucnt==0)
                          {
                            if (!(f3s==f[3] && f2s==f[2] && f1s==f[1] && f0s==f[0]))
                              {
                                xnptless1u ++;
                                xnptless2u += f_mult;
                                i = find_code(codes[1], codes_u, ncodes_u);
                                if (i==-1)
                                  {
                                    i = ncodes_u;
                                    codes_u[i] = codes[1];
                                    keep_ucode = 1;
                                    code_counts_u[i] = 0;
                                    ncodes_u ++;
                                  }
                                code_counts_u[i] += f_mult;
                                if (output_polynomials)
                                  {
                                    printf ("%d u ", p);
                                    printf ("[1,0,%d,%d,%d,%d,%d,%d,%d] ", f[6],f[5],f[4],f[3],f[2],f[1],f[0]);
                                    printf("%s ", codes[1]);
                                    printf("%d ", f_mult);
                                    printf("\n");
                                  }
                              }
                          }
                        /* if (!keep_code) */
                        /*   free(code); */
                        /* if (!keep_ucode) */
                        /*   free(ucode); */
                      } // end of critical block
                } // end of f[0] loop
        }     // end of f[1] loop
        }}}} // end of f[2], f[3], f[4], f[6] loops (f[5] is thread number, f[7]=0 and f[8]=1)
    }
    printf ("Checked %ld curves in %.3fs\n", 3*(long)pow(p,MAXD-2), omp_get_wtime()-start);
    printf ("#Gamma(%d,1) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2, xnptless1, p);
    printf ("#Gamma(%d,u) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2u, xnptless1u, p);

    printf ("Frequencies of signed root multiplicities\n");
    printf ("Gamma(%d,1): %d different patterns\n", MAXD, ncodes_1);
    for (i=0; i<ncodes_1; i++)
      {
        printf("%s: %ld\n", codes_1[i], code_counts_1[i]);
      }
    printf ("Gamma(%d,u): %d different patterns\n", MAXD, ncodes_u);
    for (i=0; i<ncodes_u; i++)
      {
        printf("%s: %ld\n", codes_u[i], code_counts_u[i]);
      }
    /* for (i=0; i<ncodes_1; i++) */
    /*   { */
    /*     free(codes_1[i]); */
    /*   } */
    /* for (i=0; i<ncodes_u; i++) */
    /*   { */
    /*     free(codes_u[i]); */
    /*   } */
}
