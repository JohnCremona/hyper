#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>

#define MAXD    5
#define MAXP    128

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    int xmincnt;
    long xnptless1, xnptless2; // 1 is #orbits, 2 is total: y^2=f(x)
    long xnptless1u, xnptless2u; // 1 is #orbits, 2 is total: uy^2=f(x)
    int qmap[MAXP*MAXP];
    int xmap[MAXD*MAXP];
    int i, j;
    int u; // will hold the least quadratic nonresidue
    int output_polynomials = 0;

    if ( argc < 1 ) { puts ("gamma5mod5 or gamma5mod5 1"); return 0; }
    const int p = 5;
    if (argc > 1) output_polynomials = atoi(argv[1]);

    start = omp_get_wtime();

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
      register int f0, f1, f2, f3, f4,
        df3, df2, df1,
        i, ny, cnt, ucnt, mincnt,
        *x;
      int emap[MAXP], edmap[MAXP];

      mincnt = 2*p+1;
      f3 = omp_get_thread_num();
      df2 = zmod(3*f3, p);
      for ( f4 = 0 ; f4 < 2 ; f4++ ) {  // f4 ranges over 0,1
        df3 = zmod(4*f4, p);
      for ( f2 = 0 ; f2 < p ; f2++ ) {
        df1 = zmod(2*f2, p);
        // set emap[i] = f(i)-f1*i-f0 for i in [0,p-1]
        // and edmap[i] = f'(i)-f1
          for ( i = 0 ; i < p ; i++ ) {
                x = xmap + i*MAXD - 1;  // x[j] = i^j
                emap[i] = zmod(f2*x[2]+f3*x[3]+f4*x[4]+x[5],p);
                edmap[i] = zmod(df1*x[1]+df2*x[2]+df3*x[3]+5*x[4],p);
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
                            if (f4==0)
                              xnptless2 ++;
                            else
                              {
                                xnptless1u ++;
                                xnptless2  += 2;
                                xnptless2u += 2;
                              }
                            if (output_polynomials)
                              printf ("%d 1 [1,%d,%d,%d,%d,%d]\n", p,f4,f3,f2,f1,f0);
                          }
                        if (ucnt==0)
                          {
                            xnptless1u ++;
                            if (f4==0)
                              xnptless2u ++;
                            else
                              {
                                xnptless1 ++;
                                xnptless2  += 2;
                                xnptless2u += 2;
                              }
                            if (output_polynomials)
                              printf ("%d u [1,%d,%d,%d,%d,%d]\n", p,f4,f3,f2,f1,f0);
                          }
                        if ( mincnt < xmincnt) { // update global minimum point count
                          xmincnt = mincnt;
                          /* printf ("%d smooth pts on y^2=x^5+%d*x^3+%d*x^2+%d*x+%d mod %d\n", xmincnt,f3,f2,f1,f0,p); */
                        }
                      } // end of critical block
                    }  // end of test for 0 or new record low number of smooth points
                } // end of f0 loop
          }     // end of f1 loop
      }} // end of f2,f4 loops (f3 is thread number and f5=1)
    }
    printf ("Checked %ld curves in %.3fs\n", 2*(long)pow(p,MAXD-1), omp_get_wtime()-start);
    printf ("#Gamma(%d,1) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2, xnptless1, p);
    printf ("#Gamma(%d,u) =  %ld (in %ld orbits) for p = %d\n", MAXD, xnptless2u, xnptless1u, p);
}
