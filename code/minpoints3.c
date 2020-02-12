#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <math.h>

#define MAXD    8
#define MAXP    64

int trivialgcd (int f[MAXD+1], int g[MAXD], int p);

static inline int zmod (int x, int m)
    { register int t, z;  t = (1.0/m) * x;  z = x-t*m;  if ( z < 0 ) z += m;  if ( z >= m ) z -= m;  return z; }

int main (int argc, char *argv[])
{
    double start;
    int xmincnt;
    int qmap[MAXP*MAXP];
    int xmap[MAXD*MAXP];
    int i, j, p;
    
    if ( argc < 2 ) { puts ("minpoints3 p"); return 0; }
    p = atoi(argv[1]);
    if ( p <= 3 || p > MAXP ) { printf ("p must be in [5,%d]", MAXP); return 0; }
    
    start = omp_get_wtime();
    
    // set qmap[i] = 1 + kron(i,p) for i in [0,p^2]
    memset(qmap,0,sizeof(qmap));
    qmap[0] = 1;
    for ( i = 1 ; i < p ; i++ ) qmap[zmod(i*i,p)] = 2;
    for ( i = 0 ; i < p ; i++ ) for ( j = 1 ; j < p ; j++ ) qmap[j*p+i] = qmap[i];
    
    // set xmap[MAXD*i+j] = i^(j+1) mod p for i in [0,p-1] and j in [1,MAXD]
    for ( i = 0 ; i < p ; i++ ) { xmap[MAXD*i] = i; for ( j = 1 ; j <= MAXD ; j++ ) xmap[MAXD*i+j] = zmod(i*xmap[MAXD*i+j-1],p); }

    xmincnt = 2*p+1;
    #pragma omp parallel num_threads(p)
    {
        int f[MAXD+1], df[MAXD];
        register int f0, f1, i, cnt, mincnt, *x;
        int emap[MAXP];
        
        mincnt = 2*p+1;
        f[8] = 1; f[7] = 0;
        f[5] = omp_get_thread_num();
        for ( f[6] = 0 ; f[6] < 3 ; f[6]++ ) {
        if ( f[6] == 2 ) while ( qmap[f[6]] ) f[6]++; // f[6] ranges over 0,1,c where c is least non-residue
        for ( f[4] = 0 ; f[4] < p ; f[4]++ ) {
        for ( f[3] = 0 ; f[3] < p ; f[3]++ ) {
        for ( f[2] = 0 ; f[2] < p ; f[2]++ ) {
            // set emap[i] = f(i)-f[1]*i-f[0] for i in [0,p-1]
            for ( i = 0 ; i < p ; i++ ) {
                x = xmap + i*MAXD - 1;  // x[j] = i^j
                emap[i] = zmod(f[2]*x[2]+f[3]*x[3]+f[4]*x[4]+f[5]*x[5]+f[6]*x[6]+f[7]*x[7]+f[8]*x[8],p);
            }
            for ( f1 = 0 ; f1 < p ; f1++ ) {
                for ( f0 = (f[1]?0:1) ; f0 < p ; f0++ ) {
                    for ( cnt = 0, i = 0 ; i < p ; i++ ) cnt += qmap[emap[i]+f1*i+f0];
                    if ( cnt < mincnt ) {
                        f[1] = f1; f[0] = f0;
                        for ( i = 1 ; i <= MAXD ; i++ ) df[i-1] = zmod(i*f[i],p);
                        if ( trivialgcd(f,df,p) ) {
                            mincnt = cnt;
                            #pragma omp critical(min)
                            if ( mincnt < xmincnt ) {
                                xmincnt = mincnt;
                                printf ("%d pts on y^2=x^8+%d*x^6+%d*x^5+%d*x^4+%d*x^3+%d*x^2+%d*x+%d\n", xmincnt, f[6],f[5],f[4],f[3],f[2],f[1],f[0]);
                            }
                        }
                    }
                }
            }
        }}}}
    }
    printf ("Checked %ld curves in %.3fs\n", 3*(long)pow(p,6), omp_get_wtime()-start);
}

// returns 1 if gcd of f and g has degree 0 and 0 otherwise
int trivialgcd (int f[MAXD+1], int g[MAXD], int p)
{
    int s[MAXD+1], t[MAXD+1];
    register int a, b, i;
    register int *sp, *se, *tp, *te, *xp;

    for ( i = MAXD ; i >= 0 && !f[i] ; i-- );
    if ( i < 0 ) return 0;
    se = s+i;
    for ( sp = se, tp=f+i ; sp >= s ; ) *sp-- = *tp--;
    for ( i = MAXD-1 ; i >= 0 && !g[i] ; i-- );
    if ( i < 0 ) return 0;
    te = t+i;
    for ( tp = te, sp=g+i ; tp >= t ; ) *tp-- = *sp--;
    
    while ( se > s && te > t ) {
        i = (se-s) - (te-t);
        if ( i >= 0 ) {
            a = *te;  b = *se;  xp = s+i;
            for ( sp = s ; sp < xp ; sp++ ) *sp = zmod (a*(*sp),p);
            for ( tp = t ; tp <= te ; sp++, tp++ ) *sp = zmod(a*(*sp)-b*(*tp),p);
            for ( se-- ; se >= s && !*se ; se-- );
        } else {
            a = *se;  b = *te;  xp = t-i;
            for ( tp = t ; tp < xp ; tp++ ) *tp = zmod (a*(*tp),p);
            for ( sp = s ; sp <= se ; sp++, tp++ ) *tp = zmod(a*(*tp)-b*(*sp),p);
            for ( te-- ; te >= t && !*te ; te-- );
        }
    }
    if ( se < s || te < t ) return 0;
    return 1;
}

