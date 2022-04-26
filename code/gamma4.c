#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>

#define MAXD    4
#define MAXP    64

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    int xmincnt;
    long xnptless1, xnptless2; // 1 is #orbits, 2 is total: y^2=f(x)
    long xnptless1u, xnptless2u; // 1 is #orbits, 2 is total: uy^2=f(x)
    int orbit_size, p2, half, pmod4;
    int qmap[MAXP*MAXP];
    int xmap[MAXD*MAXP];
    int i, j, p;
    int u; // will hold the least quadratic nonresidue
    int output_polynomials = 0;

    if ( argc < 2 ) { puts ("gamma4 p"); return 0; }
    p = atoi(argv[1]);
    if ( p < 3 || p > MAXP ) { printf ("p must be in [3,%d]\n", MAXP); return 0; }
    if (argc > 2) output_polynomials = atoi(argv[2]);

    start = omp_get_wtime();

    p2 = p*(p-1)/2; // size of orbits under affine transformations unless f2==0
    half = (p+1)/2;
    pmod4 = p & 3;
    printf("p = %d = %d (mod 4)\n", p, pmod4);

    // set qmap[i] = 1 + kron(i,p) for i in [0,p^2]
    memset(qmap,0,sizeof(qmap));
    qmap[0] = 1;
    for ( i = 1 ; i < p ; i++ )
      qmap[zmod(i*i,p)] = 2;
    for ( i = 0 ; i < p ; i++ )
      for ( j = 1 ; j < p ; j++ )
        qmap[j*p+i] = qmap[i];

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

    xmincnt = 2*p+1;
    xnptless1 = xnptless2 = 0;
#pragma omp parallel num_threads(p)
    {
        register int f0, f1, f2,
          df1,
          h0, h1, // potential coeffs of sqrt(f)
          f1s, f0s,
          i, ny, cnt, ucnt, mincnt,
          *x;
        int emap[MAXP], edmap[MAXP];

        mincnt = 2*p+1;
        f1 = omp_get_thread_num();
        for ( f2 = 0 ; f2 < 3 ; f2++ ) {
        if ( f2 == 2 ) f2 = u; // f2 ranges over 0,1,u where u is least non-residue
        df1 = zmod(2*f2, p);
        h0 = half*f2;
        f0s = zmod(h0*h0,p);
        f1s = 0;
        for ( i = 0 ; i < p ; i++ ) {
          x = xmap + i*MAXD - 1;  // x[j] = i^j
          emap[i] = zmod(f1*x[1]+f2*x[2]+x[4],p);
          edmap[i] = zmod(f1+df1*x[1]+4*x[3],p);
        }
          // inner loop over lowest coefficient f0:
        for ( f0 = 0 ; f0 < p ; f0++ ) {
          for ( cnt = 0, ucnt = 0, i = 0 ; i < p && (cnt==0 || ucnt==0); i++ )
            {
              ny = qmap[emap[i]+f0]; // # of y with y^2=f(i)
              // if ny==1 we have a zero and need to check that it is not a double zero
              if (ny != 1 || zmod(edmap[i],p) != 0)
                {
                  cnt += ny;
                  ucnt += 2-ny;
                }
            }
          if ( cnt < mincnt || cnt == 0 || ucnt == 0) { // update minimum point count in this thread
            if (cnt<mincnt) mincnt = cnt;
#pragma omp critical(min)
            { // critical block, can only be executed by one thread at a time
              if (cnt==0)
                {
                  xnptless1 ++;
                  xnptless2 += (f2==0? p: p2);
                  if (output_polynomials)
                    printf ("%d 1 [1,0,%d,%d,%d]\n", p,f2,f1,f0);
                }
              if (ucnt==0)
                {
                  if (!(f1s==f1 && f0s==f0))
                    {
                      xnptless1u ++;
                      xnptless2u += (f2==0? p: p2);
                      if (output_polynomials)
                        printf ("%d u [1,0,%d,%d,%d]\n", p,f2,f1,f0);
                    }
                }
              if ( mincnt < xmincnt) { // update global minimum point count
                xmincnt = mincnt;
              }
            } // end of critical block
          }  // end of test for 0 or new record low number of smooth points
        } // end of f0 loop
        } // end of f2 loop (f1 is thread number, f3=0 and f4=1)
    }
    printf ("Checked %ld curves in %.3fs\n", 3*(long)pow(p,MAXD-2), omp_get_wtime()-start);
    printf ("#Gamma(%d,1) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2, xnptless1, p);
    printf ("#Gamma(%d,u) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2u, xnptless1u, p);
}
