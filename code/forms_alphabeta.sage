# Code for densities of solubility for binary forms over Q_p

from sage.all import (divisors, moebius, prod, factorial, infinity)
from sage.all import (QQ, FunctionField, PolynomialRing, ProjectiveSpace)

Qp = FunctionField(QQ,'p')
pp = Qp.gen()

def subs(f,p):
    """Substitute p for the variable of the rational function f.
    """
    n = f.numerator()(p)
    d = f.denominator()(p)
    if d:
        return n/d
    else:
        return infinity


# Initialize dicts to store the alphas and betas but do not reset on reload!
# The alpha and beta values for subscripts 0,1 are known directly.
try:
    n = len(alpha_dict)
except NameError:
    print("Initializing alpha_i for i=0,1 to 0,1")
    alpha_dict = {0:0, 1:1}

def initialize_alpha_dicts():
    global alpha_dict
    print("Initializing alpha_i for i=0,1 to 0,1")
    alpha_dict = {0:0, 1:1}

try:
    n = len(beta_dict)
except NameError:
    print("Initializing beta_i for i=0,1 to 0,1")
    beta_dict = {0:0, 1:1}

def initialize_beta_dicts():
    global beta_dict
    print("Initializing beta_i for i=0,1 to 0,1")
    beta_dict =     {0:0, 1:1}

def initialize_alpha_beta_dicts():
    initialize_alpha_dicts()
    initialize_beta_dicts()

try:
    n = len(N_dict)
except NameError:
    N_dict = {}

def initialize_N_dict():
    global N_dict
    N_dict = {}

def initialize_all_dicts():
    initialize_alpha_beta_dicts()
    initialize_N_dict()

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t(i,p)={}: {}".format(k,d[k]))

def show_alpha_dicts():
    show1dict(alpha_dict, "alpha")

def show_beta_dicts():
    show1dict(beta_dict, "beta")

def show_dicts():
    show_alpha_dicts()
    show_beta_dicts()

def N(j):
    """The number of degree j monic irreducibles in GF(p)[X].
    """
    if not j in N_dict:
        N_dict[j] = sum([moebius(d)*pp**(j//d) for d in divisors(j)]) / j
    return N_dict[j]

def Ndash(j):
    """The number of degree j homogeneous irreducibles in GF(p)[X,Y] up to scaling.
    """
    return pp+1 if j==1 else N(j)

def Phi(d, base=[1,1]):
    """List of factorization patterns in degree d.  Each is a list of
    pairs [d_i,e_i] with d_i*e_i summing to d, with repeats allowed
    but unordered.
    """
    if d==0:
       yield []
    d0, e0 = base
    for di in range(d0,d+1):
        e1 = e0 if di==d0 else 1
        for ei in range(e1,(d//di)+1):
            for phi in Phi(d-di*ei,[di,ei]):
                yield [[di,ei]] + phi

def deg_fp(phi):
    """ The degree of the factorization pattern phi.
    """
    return sum(d*e for d,e in phi)

def m2(phi, jk):
    """ The number of occurrences of [d,e] in phi with de==[j,k].
    """
    return len([de for de in phi if de==jk])

def m1(phi, j):
    """ The number of occurrences of [d,e] in phi with d==j.
    """
    return len([de for de in phi if de[0]==j])

def lambda_helper(phi, NN):
    """ Helper function for affine and projective factorization probabilities.
    """
    d = deg_fp(phi)
    return prod([prod([NN(j)-i for i in
                       range(m1(phi,j))])/prod([factorial(m2(phi,[j,i]))
                                                for i in range(1,d+1)]) for j in range(1,d+1)])

def lambda_A(phi):
    """ The probability that a monic polynomial of degree deg(phi) has factorization pattern phi.
    """
    d = deg_fp(phi)
    return lambda_helper(phi, N) / pp**d

def lambda_P(phi):
    """ The probability that a homogeneous polynomial of degree deg(phi) has factorization pattern phi.
    """
    d = deg_fp(phi)
    return lambda_helper(phi, Ndash) * (pp-1)/ (pp**(d+1)-1)

def monics(F, d, u=1):
    """Iterate through all degree d polynomials over F with leading coefficient u.

    NB Use u=1 to get monics, and u=0 to give all polys of degree <d.
    """
    Fx = PolynomialRing(F,'x')
    for v in F^d:
        yield Fx(v.list()+[u])

def monics0(F, d, u=1):
    """Iterate through all degree d polynomials over F with leading
    coefficient u and next-to-leading coefficient 0

    NB Use u=1 to get monics, and u=0 to give all polys of degree <d.
    """
    Fx = PolynomialRing(F,'x')
    for v in F^(d-1):
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

def affine(L,p):
    """Returns linear combination of elements of the list L of length n,
    with coefficients

    [1-1/p, 1/p-1/p^2, ..., 1/p^(n-2)-1/p^(n-1), 1/p^(n-1)].

    Works recursively according to the definition in section 3.4.
    """
    if len(L)==1:
        return L[0]
    return ((p-1)*L[0]+affine(L[1:],p))/p

def phi_term(phi, A_or_P, v=None):
    """Helper function for beta

    The first two use A_or_P="affine" to use lambda_A while the others
    use "proj" to get lambda_P.

    beta^- and mu_0 have double=True which uses alpha^-(2*e) for (1,e) in phi.

    beta^0 and mu_1 have double=False which uses alpha^0(e) for (1,e) in phi.

    """
    lam = lambda_A(phi) if A_or_P=="affine" else lambda_P(phi)
    al = (lambda i: alpha(i,v))
    return lam * prod([1-al(e) for d,e in phi if d==1])

def beta(i, v=None, verbose=False):
    """beta_i(p).

    Computed values are stored in beta_dict keyed on i.

    For i<2 use precomputed table.  Otherwise use recursion via
    various alphas and betas.  The internal variable v keeps track of
    which of the 2 types was originally asked for so that if the same
    one appears again, instead of creating an infinite loop, the
    variable name itself is returned (as a polynomial in that
    variable).  If the computed value is a constant value (in Q(p)) it
    is returned directly and stored; if it is a (linear) polynomial in
    the same variable as associated with this function and the same
    parameters, this gives a simple linear equation to be solved so
    that a constant value (in Q(p)) can again be returned and stored;
    otherwise the returned value will be such a polynomial in some
    other variable.
    """
    try:
        return beta_dict[i]
    except KeyError:
        if i<2:
            if verbose: print("setting beta({})".format(i))
            b = beta_dict[i] = i
            return b
        pass
    make_betas(i-1)
    F = Qp
    v0 = "b_{}".format(i)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    if verbose: print("Computing beta({})".format(i))
    b = 1 - sum([phi_term(phi,"affine",v) for phi in Phi(i)])

    try:
        b=F(b)
        if verbose: print("setting beta({})".format(i))
        beta_dict[i] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("setting beta({})".format(i))
                print("{}={}".format(v0,b))
            beta_dict[i] = b
    return b

def alpha(i, v=None, verbose=False):
    """ alpha_i(p).

    Computed values are stored in alpha_dict keyed on i.
    """
    try:
        return alpha_dict[i]
    except KeyError:
        if i<2:
            if verbose: print("setting alpha({})".format(i))
            a = alpha_dict[i] = i
            return a
    make_alphas(i-1)
    F = Qp
    v0 = "a_{}".format(i)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    if verbose: print("Computing alpha({})".format(i))
    blist = []
    #print("betas used for alpha_{}".format(i))
    for j in range(i-1):
        blist += [beta(k,v) for k in range(j,-1,-1)]
        #print(list(range(j,-1,-1)))
    blist += [beta(i,v)]
    #print([i])

    if verbose: print("Computing affine({})".format(blist))
    a = affine(blist,pp)
    try:
        a=F(a)
        if verbose: print("setting alpha({})".format(i))
        alpha_dict[i] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting alpha({})".format(i))
            alpha_dict[i] = a
    return a

def make_alphas(i, verbose=False):
    """Compute (and optionally display) alpha_i
    after first computing all alphas and betas with smaller
    subscripts.
    """
    for j in range(2,i):
        make_alphas(j)
        make_betas(j)
    a = alpha(i)
    if verbose:
        print("alpha({}) = {}".format(i,a))

def make_betas(i, verbose=False):
    """Compute (and optionally display) beta_i after first computing all
    alphas and betas with smaller subscripts.

    """
    for j in range(2,i):
        make_alphas(j)
        make_betas(j)
    b = beta(i)
    if verbose:
        print("beta({}) = {}".format(i,b))

def check_value(ab,i,val):
    myval = alpha(i) if ab=="alpha" else beta(i)
    if myval==val:
        print("{}_{} OK".format(ab,i))
    else:
        print("WRONG {}_{} = {}, should be {}".format(ab,i,myval,val))

def check_alpha(i):
    """ Check that alpha_i is correct
    """
    make_alphas(i)
    val = [0, 1, 1/(2*(pp+1))][i]
    check_value("alpha",i, val)

def check_alphas():
    for i in [0,1,2]:
        check_alpha(i)


# the overall probability

def rho(d, p=pp):
    mu = (p-1) * sum(p^i * (1-alpha(d-i,p))*(1-beta(i,p)) for i in range(d+1))
    return 1 - mu / (p^(d+1) - 1)

"""
Space for comments

"""

