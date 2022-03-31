# Utility functions:
#
# - pp as generator of function field over QQ
# - substitution in ratonal function, star involution
# - lists of monic and non-monic polys and forms over any base F
# - roots of a polynomial or binary form
# - affine linear combinations

from sage.all import (FunctionField, QQ, PolynomialRing, ProjectiveSpace, VectorSpace, infinity)

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

