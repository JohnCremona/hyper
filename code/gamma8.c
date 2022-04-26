#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>

#define MAXD    8
#define MAXP    128

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    int xmincnt;
    long xnptless1, xnptless2; // 1 is #orbits, 2 is total: y^2=f(x)
    long xnptless1u, xnptless2u; // 1 is #orbits, 2 is total: uy^2=f(x)
    int orbit_size, p2, half;
    int qmap[MAXP*MAXP];
    int xmap[MAXD*MAXP];
    int i, j, p;
    int u; // will hold the least quadratic nonresidue
    int output_polynomials = 0;

    if ( argc < 2 ) { puts ("gamma8 p"); return 0; }
    p = atoi(argv[1]);
    if ( p <= 2 || p > MAXP ) { printf ("p must be in [3,%d]\n", MAXP); return 0; }
    if (argc > 2) output_polynomials = atoi(argv[2]);

    start = omp_get_wtime();

    p2 = p*(p-1)/2; // size of orbits under affine transformations unless f6==0
    half = (p+1)/2;

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
        register int f0, f1, f2, f3, f4, f5, f6,
          df5, df4, df3, df2, df1,
          h0, h1, h2, // potential coeffs of sqrt(f)
          h1h1, f3s, f2s, f1s, f0s,
          i, ny, cnt, ucnt, mincnt, is_square,
          *x;
        int emap[MAXP], edmap[MAXP];

        mincnt = 2*p+1;
        f5 = omp_get_thread_num();
        df4 = zmod(5*f5, p);
        h1 = half*f5;
        h1h1 = zmod(h1*h1, p);
        for ( f6 = 0 ; f6 < 3 ; f6++ ) {
        if ( f6 == 2 ) f6 = u; // f6 ranges over 0,1,u where u is least non-residue
        h2 = half*f6;
        f3s = zmod(2*h1*h2, p);
        df5 = zmod(6*f6, p);
        for ( f4 = 0 ; f4 < p ; f4++ ) {
          df3 = zmod(4*f4, p);
          h0 = zmod(half*(f4-h2*h2),p);
          f0s = zmod(h0*h0,p);
          f1s = zmod(2*h0*h1,p);
          f2s = zmod(2*h0*h2+h1h1,p);
        for ( f3 = 0 ; f3 < p ; f3++ ) {
          df2 = zmod(3*f3, p);
        for ( f2 = 0 ; f2 < p ; f2++ ) {
          df1 = zmod(2*f2, p);
          // set emap[i] = f(i)-f1*i-f0 for i in [0,p-1]
          // and edmap[i] = f'(i)-f1
          for ( i = 0 ; i < p ; i++ ) {
                x = xmap + i*MAXD - 1;  // x[j] = i^j
                emap[i] = zmod(f2*x[2]+f3*x[3]+f4*x[4]+f5*x[5]+f6*x[6]+x[8],p);
                edmap[i] = zmod(df1*x[1]+df2*x[2]+df3*x[3]+df4*x[4]+df5*x[5]+ 8*x[7],p);
            }
          // inner loop over lowest two coefficients, f1 and f0:
          for ( f1 = 0 ; f1 < p ; f1++ ) {
            for ( f0 = 0 ; f0 < p ; f0++ ) {
              for ( cnt = 0, ucnt = 0, i = 0 ; i < p && (cnt==0 || ucnt==0); i++ )
                      {
                        ny = qmap[emap[i]+f1*i+f0]; // # of y with y^2=f(i)
                        // if ny==1 we have a zero and need to check that it is not a double zero
                        if (ny != 1 || zmod(edmap[i]+f1,p) != 0)
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
                            xnptless2 += (f6==0? p: p2);
                            if (output_polynomials)
                              printf ("%d 1 [1,0,%d,%d,%d,%d,%d,%d,%d]\n", p,f6,f5,f4,f3,f2,f1,f0);
                          }
                        if (ucnt==0)
                          {
                            if (!(f3s==f3 && f2s==f2 && f1s==f1 && f0s==f0))
                              {
                                xnptless1u ++;
                                xnptless2u += (f6==0? p: p2);
                                if (output_polynomials)
                                  printf ("%d u [1,0,%d,%d,%d,%d,%d,%d,%d]\n", p,f6,f5,f4,f3,f2,f1,f0);
                              }
                          }
                        if ( mincnt < xmincnt) { // update global minimum point count
                          xmincnt = mincnt;
                          /* printf ("%d smooth pts on y^2=x^8+%d*x^6+%d*x^5+%d*x^4+%d*x^3+%d*x^2+%d*x+%d mod %d\n", xmincnt, f6,f5,f4,f3,f2,f1,f0,p); */
                        }
                      } // end of critical block
                    }  // end of test for 0 or new record low number of smooth points
                } // end of f0 loop
          }     // end of f1 loop
        }}}} // end of f2, f3, f4, f6 loops (f5 is thread number, f7=0 and f8=1)
    }
    printf ("Checked %ld curves in %.3fs\n", 3*(long)pow(p,MAXD-2), omp_get_wtime()-start);
    printf ("#Gamma(%d,1) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2, xnptless1, p);
    printf ("#Gamma(%d,u) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2u, xnptless1u, p);
}
