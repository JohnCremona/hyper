# Utility functions:
#
# - pp as generator of function field over QQ
# - substitution in ratonal function, star involution
# - lists of monic and non-monic polys and forms over any base F
# - roots of a polynomial or binary form
# - affine linear combinations

from sage.all import (FunctionField, QQ, PolynomialRing, ProjectiveSpace, VectorSpace, infinity)
from collections import Counter

Qp = FunctionField(QQ,'p')
pp = Qp.gen()

def subs(f,p):
    """Substitute p for the variable of the rational function f.
    """
    if f in QQ:
        return f
    n = f.numerator()(p)
    d = f.denominator()(p)
    if d:
        return n/d
    else:
        return infinity

def star(r):
    return r if r in QQ else subs(r,1/pp)

def monics(F, d, u=1):
    """Iterate through all degree d polynomials over F with leading coefficient u.

    NB Use u=1 to get monics, and u=0 to give all polys of degree <d.
    """
    Fx = PolynomialRing(F,'x')
    for v in VectorSpace(F,d):
        yield Fx(v.list()+[u])

def monics0(F, d, u=1):
    """Iterate through all degree d polynomials over F with leading
    coefficient u and next-to-leading coefficient 0

    NB Use u=1 to get monics, and u=0 to give all polys of degree <d.
    """
    Fx = PolynomialRing(F,'x')
    for v in VectorSpace(F,d-1):
        yield Fx(v.list()+[0,u])

def homog(F, d):
    """ List of homogeneous polynomials in F[X,Y] of degree d, up to scaling.
    """
    Fx = PolynomialRing(F,'x')
    Fxy = PolynomialRing(F,['x','y'])
    x, y = Fxy.gens()
    def homog(f):
        return Fxy(y**d * f(x/y))
    return [homog(Fx(list(v))) for v in ProjectiveSpace(F,d)]

def roots(f):
    """returns list of pairs (a,j) where a is a root of
    multiplicity j>0.  In the homogeneous case this will
    include a=infinity when deg(f(x,1))<deg(f(x,y)).
    """
    if f.parent().ngens()==1:
        return [(a,j) for a,j in f.roots()]
    # homogeneous case
    R1 = PolynomialRing(f.base_ring(),'x')
    x = R1.gen()
    f1 = f([x,1])
    j=f.degree()-f1.degree()
    res = [(infinity,j)] if j else []
    return res + roots(f1)

def eps(f,a,j):
    """Given the root a of multiplicity j, when j is even returns the
    sign of the leading coefficient in the series expansion of f about
    x=a, or +1 when j is odd.
    """
    x = f.parent().gen()
    return +1 if j%2==1 or (f//(x-a)**j)(a).is_square() else -1

def signed_roots(f):
    """returns list of triples (a,j,eps) where a is a root of
    multiplicity j>0 and (for even j) eps in [-1,+1] is the quadratic
    character of (f(x)/(x-a)^j)(a).  In the homogeneous case this will
    include a=infinity when deg(f(x,1))<deg(f(x,y)).
    """
    if f.parent().ngens()==1:
        return [(a,j,eps(f,a,j)) for a,j in f.roots()]
    # homogeneous case
    R1 = PolynomialRing(f.base_ring(),'x')
    x = R1.gen()
    f1 = f([x,1])
    j=f.degree()-f1.degree()
    res = []
    if j:
        res = [(infinity,j,1 if j%2==1 or f1.leading_coefficient().is_square() else -1)]
    return res + signed_roots(f1)

def f_multiplicity(f):
    """For f in a restricted list of polys of degree n, up to affine
    transformation (with p not dividing 2*n), assuming f[n-1]=0, the
    multiplicity is

    p if f[n-2]=0
    (p-1)/2 if f[n-2]!=0 and p=3 (mod 4) or n even
    (p-1)/4 if f[n-2]!=0 and p=1 (mod 4) and n odd

    """
    p = f.parent().characteristic()
    n = f.degree()
    if p==2:
        return 1
    if n%p==0:
        return 1 if f[n-1]==0 else p-1 if n%2==0 else (p-1)/2
    else:
        return p if f[n-2]==0 else p*(p-1)/2 if (p%4==3 or n%2==0) else p*(p-1)/4

def root_multiplicities(f):
    return tuple(sorted(((j,eps(f,a,j)) for a,j in f.roots())))

def root_multiplicity_counts(flist):
    c = Counter()
    for f in flist:
        c[root_multiplicities(f)] += f_multiplicity(f)
    return c

def affine(L,p):
    """Returns linear combination of elements of the list L of length n,
    with coefficients

    [1-1/p, 1/p-1/p^2, ..., 1/p^(n-2)-1/p^(n-1), 1/p^(n-1)].

    Works recursively according to the definition in section 3.4.
    """
    if len(L)==1:
        return L[0]
    return ((p-1)*L[0]+affine(L[1:],p))/p

def partitions(n, k): # into exactly k non-negative ordered summands
    if k==0:
        return []
    if k==1:
        return [[n]]
    if n==0:
        return [[0 for _ in range(k)]]
    return sum([[[a]+s for s in partitions(n-a,k-1)] for a in range(n+1)], [])

def x_multiplicity(f,h,x0=0):
    r""" returns (i,eps) where i is the multiplcity of x=x0 on z^2+h(x)*z=f(x)
    and (for i even and positive) eps is +1 or -1 according as the leading
    quadratic is split or not.

    Here f and h are in GF(2)[x].
    """
    x = f.parent().gen()
    if x0!=0:
        return x_multiplicity(f(x+x0),h(x+x0))
    # Now x0=0
    e=0; m=0
    while True:
        c = [f[m],h[e]]
        if c==[1,1]: return [m,-1]
        if c==[0,1]: return [m,+1]
        if c==[1,0]:
            f += x**m+h*x**e
        assert [f[m],h[e]]==[0,0]
        if f==h==0:
            return infinity
        m += 1
        if f[m]: return [m,+1]
        e += 1
        m += 1
        print(f,h)

def point_multiplicity(f,h,P=[0,0]):
    r""" returns (i,eps) where i is the multiplcity of P on z^2+h(x)*z=f(x)
    and (for i even and positive) eps is +1 or -1 according as the
    point is split or not.

    Here f and h are in GF(2)[x].
    """
    x = f.parent().gen()
    if P[0]==1: # x=1, shift to 0
        return point_multiplicity(f(x+1),h(x+1),[0,P[1]])
    if P[1]==1: # z=1, shift to 0
        return point_multiplicity(f+1+h,h,[P[0],0])
    # Now P=[0,0]
    if f[0]: return [0,0]
    if [f[1],h[0]]!=[0,0]: return [1,0]
    e=1; m=2
    while e<=h.degree() or m<=f.degree():
        c = [f[m],h[e]]
        if c==[1,1]: return [m,-1]
        if c==[0,1]: return [m,+1]
        if c==[1,0]:
            f += x**(m)+h*x**e
        assert [f[m],h[e]]==[0,0]
        m += 1
        if f[m]: return [m,+1]
        e += 1
        m += 1

def point_multiplicities(f,h):
    r""" returns a list of up to 4 (P,[i,eps]) where i>0 is the multiplcity
    of P on z^2+h(x)*z=f(x) and (for i even) eps is +1 or -1 according
    as the point is split or not.

    Here f and h are in GF(2)[x].
    """
    res = [(P,point_multiplicity(f,h,P)) for P in [[0,0],[1,0],[0,1],[1,1]]]
    return [m for m in res if m[1][0]]

