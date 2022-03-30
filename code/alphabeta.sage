from sage.all import (prod, polygen, infinity)
from sage.all import (QQ, ZZ, GF, PolynomialRing)
from basics import Qp,pp, signed_roots, affine
from fact_pat import (initialize_N_dict, lambda_A, lambda_P, Phi)
from gamma import initialize_Gamma_dicts, Gamma_plus, Gamma_minus

# Initialize dicts to store the betas and alphas but do not reset on reload!
# The beta and alpha values for subscripts 0,1,2 are known directly.
try:
    n = len(beta_0_dict)
except NameError:
    print("Initializing beta(i,p) for i=0,1,2 to 0,1,1/2")
    beta_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(beta_plus_dict)
except NameError:
    print("Initializing beta(i,1) for i=0,1,2 to 1,1,1/p with p={}".format(pp))
    beta_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1/pp}
try:
    n = len(beta_minus_dict)
except NameError:
    print("Initializing beta(i,u) for i=0,1,2 to 0,1,1/(p+1) with p={}".format(pp))
    beta_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

def initialize_beta_dicts():
    global beta_0_dict, beta_plus_dict, beta_minus_dict
    print("Initializing beta(i,p) for i=0,1,2 to 0,1,1/2")
    beta_0_dict =      {(0,pp):0, (1,pp):1, (2,pp):1/2}
    print("Initializing beta(i,1) for i=0,1,2 to 1,1,1/p with p={}".format(pp))
    beta_plus_dict =   {(0,pp):1, (1,pp):1, (2,pp):1/pp}
    print("Initializing beta(i,u) for i=0,1,2 to 0,1,1/(p+1) with p={}".format(pp))
    beta_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

try:
    n = len(alpha_0_dict)
except NameError:
    print("Initializing alpha(i,p) for i=0,1,2 to 0,1,1/2")
    alpha_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(alpha_plus_dict)
except NameError:
    print("Initializing alpha(i,1) for i=0,1,2 to 1,1,1")
    alpha_plus_dict = {(0,pp):1, (1,pp):1, (2,pp):1}
try:
    n = len(alpha_minus_dict)
except NameError:
    print("Initializing alpha(i,u) for i=0,1,2 to 0,1,p/(p+1) with p={}".format(pp))
    alpha_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

def initialize_alpha_dicts():
    global alpha_0_dict, alpha_plus_dict, alpha_minus_dict
    print("Initializing alpha(i,p) for i=0,1,2 to 0,1,1/2")
    alpha_0_dict =     {(0,pp):0, (1,pp):1, (2,pp):1/2}
    print("Initializing alpha(i,1) for i=0,1,2 to 1,1,1")
    alpha_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1}
    print("Initializing alpha(i,u) for i=0,1,2 to 0,1,p/(p+1) with p={}".format(pp))
    alpha_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

def initialize_alpha_beta_dicts():
    initialize_alpha_dicts()
    initialize_beta_dicts()

def initialize_all_dicts():
    initialize_alpha_beta_dicts()
    #initialize_Delta_dicts()
    initialize_Gamma_dicts()
    initialize_N_dict()

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t(i,p)={}: {}".format(k,d[k]))

def show_beta_dicts():
    show1dict(beta_0_dict, "beta(n,p)")
    show1dict(beta_plus_dict, "beta(n,1)")
    show1dict(beta_minus_dict, "beta(n,u)")

def show_alpha_dicts():
    show1dict(alpha_0_dict, "alpha(n,p)")
    show1dict(alpha_plus_dict, "alpha(n,1)")
    show1dict(alpha_minus_dict, "alpha(n,u)")

def show_dicts():
    show_alpha_dicts()
    show_beta_dicts()

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


# The R() and r() functions are no longer used in the code but are
# here since they are defined in the text.  Here we instead loop over
# all roots (including infinity in the projective case) to compute the
# f_terms for f in one of the Gamma sets.

def R(j,f):
    # set of roots of f of multiplicity j
    return [a for a,e in f.roots() if e==j]

def r(j,f):
    if f.parent().ngens()==1: # inhomogeneous case
        return len(R(j,f))
    # else homogeneous case
    x = polygen(f.base_ring())
    f1 = f([x,1])
    # the second term is 1 iff infinity has mult j
    return r(j,f1) + int(f.degree()==j+f1.degree())

def Rplus(j,f):
    if j%2==1:
       return R(j,f)
    x = f.parent().gen()
    return [a for a in R(j,f) if (f//(x-a)**j)(a).is_square()]

def rplus(j,f):
    if j%2==1:
       return r(j,f)
    if f.parent().ngens()==1:
        return len(Rplus(j,f))
    # homogeneous case
    R1 = PolynomialRing(f.base_ring(),'x')
    x = R1.gen()
    f1 = f([x,1])
    return len(Rplus(j,f1)) + int((f.degree()==j+f1.degree()) and (f1.leading_coefficient().is_square()))

def Rminus(j,f):
    if j%2==1:
        return []
    x = f.parent().gen()
    return [a for a in R(j,f) if not (f//(x-a)**j)(a).is_square()]

def rminus(j,f):
    if j%2==1:
       return 0
    if f.parent().ngens()==1:
        return len(Rminus(j,f))
    # homogeneous case
    R1 = PolynomialRing(f.base_ring(),'x')
    x = R1.gen()
    f1 = f([x,1])
    return len(Rminus(j,f1)) + int((f.degree()==j+f1.degree()) and not (f1.leading_coefficient().is_square()))

def beta_eps(eps):
    """ Return the function beta(-,u), beta(-,p) or beta(-,1) according to eps=-1,0,+1.
    """
    try:
        return [beta_minus,beta_0,beta_plus][eps+1]
    except IndexError:
        return beta

def f_term(f,p=pp):
    """Helper function for alpha(-,eps), mu_0.  In the paper this is
    expressed differently, as a double product over j up to the degree
    and eps, with multiplicities.  Here we just take the product over
    all roots.

    Note that if there is a root of multiplicity 1 then beta(1,eps)=1
    and the result is 0, but this will only be called with f which
    have no such roots.

    This works equally well in the projective case.
    """
    if p==pp: # will not be called in this case anyway
        return 0
    return prod([(1-beta_eps(eps)(j,p)) for a,j,eps in signed_roots(f)])

def fh_term(f,h):
    """Helper function for alpha(-,eps), mu_0 in case p=2.  In the paper
    this is expressed differently, as a double product over j up to
    the degree and eps, with multiplicities.  Here we just take the
    product over all roots.

    Note that if there is a root of multiplicity 1 then beta(1,eps)=1
    and the result is 0, but this will only be called with f which
    have no such roots.

    This works equally well in the projective case.

    """
    return prod([(1-beta_eps(eps)(j,2)) for P,(j,eps) in point_multiplicities(f,h)])

def phi_term(phi, A_or_P, double, p, v=None):
    """Helper function for alpha(-,p), alpha(-,u), mu_0, mu_1.

    The first two use A_or_P="affine" to use lambda_A while the others
    use "proj" to get lambda_P.

    alpha(-,u) and mu_0 have double=True which uses beta(2*e,u) for (1,e) in phi.

    alpha(-,p) and mu_1 have double=False which uses beta(e,p) for (1,e) in phi.

    """
    lam = lambda_A(phi,p) if A_or_P=="affine" else lambda_P(phi,p)
    al = (lambda i: beta_minus(2*i,p,v)) if double else (lambda i: beta_0(i,p,v))
    return lam * prod([1-al(e) for d,e in phi if d==1])

def alpha(i,p=pp,v=None):
    """ Average of alpha(i,1) and alpha(i,u)
    """
    return (alpha_plus(i,p,v)+alpha_minus(i,p,v))/2

def beta(i,p=pp,v=None):
    """ Average of beta(i,1) and beta(i,u)
    """
    return (beta_plus(i,p,v)+beta_minus(i,p,v))/2

def alpha_plus(i,p=pp,v=None, verbose=False):
    """alpha(i,1; p).

    Computed values are stored in alpha_plus_dict keyed on (i,p).

    For i<3 use precomputed table.  Otherwise use recursion via
    various betas and alphas.  The internal variable v keeps track of
    which of the 6 types was originally asked for so that if the same
    one appears again, instead of creating an infinite loop, the
    variable name itself is returned (as a polynomial in that
    variable).  If the computed value is a constant value (in Q or
    Q(p)) it is returned directly and stored; if it is a (linear)
    polynomial in the same variable as associated with this function
    and the same parameters, this gives a simple linear equation to be
    solved so that a constant value (in Q or Q(p)) can again be
    returned and stored; otherwise the returned value will be such a
    polynomial in some other variable.
    """
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_plus({},{})".format(i,p))
            b = alpha_plus_dict[(i,p)] = 1
            return b
        pass
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "bp_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (i)
    if verbose: print("Computing alpha_plus({},{})".format(i,p))
    Fp = GF(p) if p in ZZ else None
    G = Gamma_plus(i,Fp)
    if p==2:
        e = (3*i+1)//2 if i%2 else 3*i//2
        b = 1 - sum([fh_term(f,h) for f,h in G])/p**e
    else:
        b = 1 - sum([f_term(f,p) for f in G])/p**i

    try:
        b=F(b)
        if verbose: print("setting alpha_plus({},{})".format(i,p))
        alpha_plus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("setting alpha_plus({},{})".format(i,p))
                print("{}={}".format(v0,b))
            alpha_plus_dict[(i,p)] = b
    return b

def alpha_minus(i,p=pp,v=None, verbose=False):
    """alpha(i,u; p).

    Computed values are stored in alpha_minus_dict keyed on (i,p).
    """
    try:
        return alpha_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_minus({},{})".format(i,p))
            b = alpha_minus_dict[(i,p)] = [0,1,p/(p+1)][i]
            return b
    if i%2==1:
        if verbose: print("setting alpha_minus({},{})".format(i,p))
        b = alpha_minus_dict[(i,p)] = alpha_plus(i,p,v)
        return b
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "bm_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # now i is even, use Prop 3.3(ii)
    if verbose: print("Computing alpha_minus({},{})".format(i,p))
    i2 = i//2
    Fp = GF(p) if p in ZZ else None
    G = Gamma_minus(i,Fp)
    if p==2:
        b = ( 1
              - sum([phi_term(phi,"affine",True,p,v) for phi in Phi(i2)]) / p**i2
              - sum([fh_term(f,h) for f,h in G]) / p**((3*i)//2))
    else:
        b = ( 1
              - sum([phi_term(phi,"affine",True,p,v) for phi in Phi(i2)]) / p**i2
              - sum([f_term(f,p) for f in G]) / p**i)
    try:
        b=F(b)
        if verbose: print("setting alpha_minus({},{})".format(i,p))
        alpha_minus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("{}={}".format(v0,b))
                print("setting alpha_minus({},{})".format(i,p))
            alpha_minus_dict[(i,p)] = b
    return b

def alpha_0(i,p=pp,v=None, verbose=False):
    """alpha(i,p; p).

    Computed values are stored in alpha_0_dict keyed on (i,p).
    """
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_0({},{})".format(i,p))
            b =  alpha_0_dict[(i,p)] = [0,1,1/2][i]
            return b
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "b0_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (iii)
    if verbose: print("Computing alpha_0({},{})".format(i,p))
    b = 1 - sum([phi_term(phi,"affine",False,p,v) for phi in Phi(i)])
    try:
        b=F(b)
        if verbose: print("setting alpha_0({},{})".format(i,p))
        alpha_0_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("{}={}".format(v0,b))
                print("setting alpha_0({},{})".format(i,p))
            alpha_0_dict[(i,p)] = b
    return b

def beta_0(i,p=pp,v=None, verbose=False):
    """ beta(i,p; p).

    Computed values are stored in beta_0_dict keyed on (i,p).
    """
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_0({},{})".format(i,p))
            a = beta_0_dict[(i,p)] = [0,1,1/2][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "a0_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    make_betas(i-1,p)
    if verbose: print("Computing beta_0({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [alpha(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [alpha_0(k,p,v) for k in range(j,-1,-1)]
    if i%2==0:
       blist += [alpha_0(i,p,v)]
    else:
       blist += [alpha(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        if verbose: print("setting beta_0({},{})".format(i,p))
        beta_0_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting beta_0({},{})".format(i,p))
            beta_0_dict[(i,p)] = a
    return a

def beta_plus(i,p=pp,v=None, verbose=False):
    """ beta(i,1; p).

    Computed values are stored in beta_plus_dict keyed on (i,p).
    """
    try:
        return beta_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_plus({},{})".format(i,p))
            a = beta_plus_dict[(i,p)] = [1,1,1/p][i]
            return a
    make_betas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "ap_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    if verbose: print("Computing beta_plus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [alpha_0(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [alpha(k,p,v) for k in range(j,-1,-1)]
    if i%2==0:
       blist += [alpha_plus(i,p,v)]
    else:
       blist += [alpha_0(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        if verbose: print("setting beta_plus({},{})".format(i,p))
        beta_plus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting beta_plus({},{})".format(i,p))
            beta_plus_dict[(i,p)] = a
    return a

def beta_minus(i,p=pp,v=None, verbose=False):
    """ beta(i,u; p).

    Computed values are stored in beta_minus_dict keyed on (i,p).
    """
    try:
        return beta_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_minus({},{})".format(i,p))
            a = beta_minus_dict[(i,p)] = [0,1,1/(p+1)][i]
            return a
    if i%2==1:
        if verbose: print("setting beta_minus({},{})".format(i,p))
        beta_minus_dict[(i,p)] = beta_plus(i,p)
        return beta_minus_dict[(i,p)]
    make_betas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "am_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    if verbose: print("Computing beta_minus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [alpha_0(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [alpha(k,p,v) for k in range(j,-1,-1)]
    blist += [alpha_minus(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        if verbose: print("setting beta_minus({},{})".format(i,p))
        beta_minus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting beta_minus({},{})".format(i,p))
            beta_minus_dict[(i,p)] = a
    return a

def make_betas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 betas with subscript i
    after first computing all betas and alphas with smaller
    subscripts.
    """
    if verbose:
        print("Making all beta_{} for p={}".format(i,p))
    for j in range(3,i):
        make_betas(j,p)
        make_alphas(j,p)
    a = beta_plus(i,p)
    if verbose:
        print("beta_plus({},{}) = {}".format(i,p,a))
    a = beta_minus(i,p)
    if verbose:
        print("beta_minus({},{}) = {}".format(i,p,a))
    a = beta_0(i,p)
    if verbose:
        print("beta_0({},{}) = {}".format(i,p,a))

def make_alphas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 alphas with subscript i
    after first computing all betas and alphas with smaller
    subscripts.
    """
    for j in range(3,i):
        make_betas(j,p)
        make_alphas(j,p)
    b = alpha_plus(i,p)
    if verbose:
        print("alpha_plus({},{}) = {}".format(i,p,b))
    b = alpha_minus(i,p)
    if verbose:
        print("alpha_minus({},{}) = {}".format(i,p,b))
    b = alpha_0(i,p)
    if verbose:
        print("alpha_0({},{}) = {}".format(i,p,b))

def check_value(ab,i,eps,val,p=pp):
    myval = [beta_minus,beta_0,beta_plus][eps+1](i,p) if ab=="beta" else [alpha_minus,alpha_0,alpha_plus][eps+1](i,p)
    #oldsup = ["-","0","+"][eps+1]
    sup = ["u","p","1"][eps+1]
    #oldsymb = "{}_{}^{}({})".format(ab,i,oldsup,p)
    symb = "{}({},{}; {})".format(ab,i,sup,p)
    if myval==val:
        print("{} OK".format(symb, p))
    else:
        print("WRONG {} = {}, should be {}".format(symb,myval,val))

def check3():
    """ Check that all 3 beta(3,eps; p) are correct for p=3 and p generic.
    """
    make_betas(3,3)
    check_value("beta",3,+1, 50246/177147, 3)
    check_value("beta",3,-1, 50246/177147, 3)
    check_value("beta",3 ,0, 431/729,3)

    make_betas(3)
    check_value("beta",3,+1, (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8))
    check_value("beta",3,-1, (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8))
    check_value("beta",3, 0, (pp**3+pp**2-2*pp+2)/(2*pp**3))

    make_betas(3,2)
    check_value("beta",3,+1, 807/2048, 2)
    check_value("beta",3,-1, 807/2048, 2)
    check_value("beta",3 ,0, 39/64,2)


def check4():
    """ Check that all 3 beta(4,eps; p) are correct for p=3, p=5 and p generic.
    """
    make_betas(4,3)
    make_betas(4,5)
    make_betas(4)
    check_value("beta",4,+1, 16600/59049, 3)
    check_value("beta",4,+1, 352624/1953125, 5)
    check_value("beta",4,+1, (pp**2+1)*(2*pp**3-pp**2-2*pp+2)/(2*pp**6))

    check_value("beta",4,-1, (2*pp**10+3*pp**9-pp**5+2*pp**4-2*pp**2-3*pp-1)/(2*(pp+1)**2 *(pp**9-1)))
    check_value("beta",4, 0, (4*pp**10+8*pp**9-4*pp**8+4*pp**6-3*pp**4+pp**3-5*pp-5)/(8*(pp+1)*(pp**9-1)))

    make_betas(4,2)
    check_value("beta",4,+1, 407079/1048576, 2)
    check_value("beta",4,-1, 3569/9198, 2)
    check_value("beta",4 ,0, 7369/12264,2)


def check5():
    """ Check that all beta(5,eps; p) and alpha(5,eps; p) are correct for p=3.
    """
    make_betas(5,3)
    check_value("beta",5, 0, 1493687989147/2541865828329, 3)
    check_value("beta",5,+1, 13670659773280445407/48630661836227715204, 3)
    check_value("beta",5,-1, 13670659773280445407/48630661836227715204, 3)
    check_value("beta",5,+1,(pp**26 + 1/2*pp**25 - 1/2*pp**24 + 1/2*pp**23 - 1/2*pp**22 + pp**20 - 1/2*pp**19 - 11/30*pp**17 + 2/15*pp**16 - 1/12*pp**15 + 1/6*pp**14 - 3/10*pp**13 + 1/5*pp**12 + 1/4*pp**11 - 1/3*pp**7 + 1/6*pp**5 - 5/6*pp**3 + 3/2*pp**2 + pp - 1)/(pp**27 + pp**26))
    check_value("beta",5,-1,(pp**26 + 1/2*pp**25 - 1/2*pp**24 + 1/2*pp**23 - 1/2*pp**22 + pp**20 - 1/2*pp**19 - 11/30*pp**17 + 2/15*pp**16 - 1/12*pp**15 + 1/6*pp**14 - 3/10*pp**13 + 1/5*pp**12 + 1/4*pp**11 - 1/3*pp**7 + 1/6*pp**5 - 5/6*pp**3 + 3/2*pp**2 + pp - 1)/(pp**27 + pp**26))
    check_value("beta",5,0,(1/2*pp**13 + pp**12 - 1/2*pp**11 + 1/2*pp**9 - 1/3*pp**7 + 1/6*pp**5 - 5/6*pp**3 + 3/2*pp**2 + pp - 1)/(pp**13 + pp**12))

    make_alphas(5,3)
    check_value("alpha",5, 0, 129514464056263/205891132094649, 3)
    check_value("alpha",5,+1, 160260073/172186884, 3)
    check_value("alpha",5,-1, 160260073/172186884, 3)
    check_value("alpha",5,+1,1)
    check_value("alpha",5,-1,1)
    check_value("alpha",5,0,  (19/30*pp**17 + 19/30*pp**16 - 1/12*pp**15 + 1/6*pp**14 - 3/10*pp**13 + 1/5*pp**12 + 1/4*pp**11 - 1/3*pp**7 + 1/6*pp**5 - 5/6*pp**3 + 3/2*pp**2 + pp - 1)/(pp**17 + pp**16))

def check6():
    """ Check that all beta(6,eps; p) and alpha(6,eps; p) are correct for p=3.
    """
    make_betas(6,3)
    check_value("beta",6, 0, 26377476341107224253/44887561041873369600, 3)
    check_value("beta",6,+1, 605398279518845051650813/2153584544086426253951538, 3)
    check_value("beta",6,-1, 27339928051320364957/97256382257392300800, 3)
    check_value("beta",6,+1,(pp**24 + 1/2*pp**23 + 1/2*pp**22 + pp**21 + pp**19 + pp**18 + 1/2*pp**17 + pp**16 - 7/8*pp**15 + 2/3*pp**14 - 1/2*pp**13 + 5/24*pp**12 + 1/2*pp**11 - 3/2*pp**10 + 3/2*pp**9 + 1/2*pp**8 + 1/2*pp**6 + 1/3*pp**5 + 1/2*pp**4 + 1/6*pp**3 + 1/2*pp**2 + pp - 1)/(pp**25 + pp**24 + pp**23 + pp**22 + pp**21 + pp**20 + pp**19 + pp**18 + pp**17))
    check_value("beta",6,-1,(pp**28 + 7/2*pp**27 + 6*pp**26 + 17/2*pp**25 + 11*pp**24 + 13*pp**23 + 16*pp**22 + 39/2*pp**21 + 45/2*pp**20 + 193/8*pp**19 + 577/24*pp**18 + 24*pp**17 + 191/8*pp**16 + 583/24*pp**15 + 24*pp**14 + 23*pp**13 + 25*pp**12 + 53/2*pp**11 + 51/2*pp**10 + 73/3*pp**9 + 71/3*pp**8 + 121/6*pp**7 + 37/2*pp**6 + 47/3*pp**5 + 41/3*pp**4 + 55/6*pp**3 + 14/3*pp**2 + 13/6*pp + 2/3)/(pp**29 + 4*pp**28 + 8*pp**27 + 12*pp**26 + 16*pp**25 + 20*pp**24 + 24*pp**23 + 28*pp**22 + 32*pp**21 + 35*pp**20 + 36*pp**19 + 36*pp**18 + 36*pp**17 + 36*pp**16 + 36*pp**15 + 36*pp**14 + 36*pp**13 + 36*pp**12 + 36*pp**11 + 36*pp**10 + 35*pp**9 + 32*pp**8 + 28*pp**7 + 24*pp**6 + 20*pp**5 + 16*pp**4 + 12*pp**3 + 8*pp**2 + 4*pp + 1))
    check_value("beta",6,0,(1/2*pp**35 + 5/2*pp**34 + 5*pp**33 + 7*pp**32 + 19/2*pp**31 + 25/2*pp**30 + 91/6*pp**29 + 35/2*pp**28 + 20*pp**27 + 133/6*pp**26 + 22*pp**25 + 22*pp**24 + 49/2*pp**23 + 26*pp**22 + 103/4*pp**21 + 3775/144*pp**20 + 473/18*pp**19 + 105/4*pp**18 + 3751/144*pp**17 + 1907/72*pp**16 + 79/3*pp**15 + 177/8*pp**14 + 439/24*pp**13 + 33/2*pp**12 + 1003/72*pp**11 + 211/18*pp**10 + 147/16*pp**9 + 56/9*pp**8 + 271/72*pp**7 + 95/48*pp**6 + 11/8*pp**5 + 17/24*pp**4 - 1/2*pp - 1/2)/(pp**35 + 4*pp**34 + 8*pp**33 + 12*pp**32 + 16*pp**31 + 20*pp**30 + 24*pp**29 + 28*pp**28 + 32*pp**27 + 35*pp**26 + 36*pp**25 + 36*pp**24 + 36*pp**23 + 36*pp**22 + 36*pp**21 + 36*pp**20 + 36*pp**19 + 36*pp**18 + 36*pp**17 + 36*pp**16 + 35*pp**15 + 32*pp**14 + 28*pp**13 + 24*pp**12 + 20*pp**11 + 16*pp**10 + 12*pp**9 + 8*pp**8 + 4*pp**7 + pp**6))

    make_alphas(6,3)
    check_value("alpha",6, 0, 690037935950003/1098030248972800, 3)
    check_value("alpha",6,+1, 28366779023771/30502389939948, 3)
    check_value("alpha",6,-1, 9541669997405587/10262359634630400, 3)
    check_value("alpha",6,+1,1)
    check_value("alpha",6,-1,(pp**31 + 4*pp**30 + 8*pp**29 + 11*pp**28 + 13*pp**27 + 29/2*pp**26 + 103/6*pp**25 + 56/3*pp**24 + 133/6*pp**23 + 68/3*pp**22 + 68/3*pp**21 + 127/6*pp**20 + 62/3*pp**19 + 65/3*pp**18 + 139/6*pp**17 + 193/8*pp**16 + 577/24*pp**15 + 24*pp**14 + 191/8*pp**13 + 583/24*pp**12 + 23*pp**11 + 19*pp**10 + 17*pp**9 + 31/2*pp**8 + 25/2*pp**7 + 59/6*pp**6 + 15/2*pp**5 + 5*pp**4 + 7/3*pp**3 + 3/2*pp**2 + 2*pp + 1)/(pp**31 + 4*pp**30 + 8*pp**29 + 12*pp**28 + 16*pp**27 + 20*pp**26 + 24*pp**25 + 28*pp**24 + 32*pp**23 + 35*pp**22 + 36*pp**21 + 36*pp**20 + 36*pp**19 + 36*pp**18 + 36*pp**17 + 36*pp**16 + 36*pp**15 + 36*pp**14 + 36*pp**13 + 36*pp**12 + 35*pp**11 + 32*pp**10 + 28*pp**9 + 24*pp**8 + 20*pp**7 + 16*pp**6 + 12*pp**5 + 8*pp**4 + 4*pp**3 + pp**2))
    check_value("alpha",6,0,(91/144*pp**29 + 91/36*pp**28 + 5*pp**27 + 1075/144*pp**26 + 719/72*pp**25 + 37/3*pp**24 + 117/8*pp**23 + 427/24*pp**22 + 21*pp**21 + 1651/72*pp**20 + 218/9*pp**19 + 1169/48*pp**18 + 427/18*pp**17 + 1711/72*pp**16 + 1159/48*pp**15 + 187/8*pp**14 + 545/24*pp**13 + 49/2*pp**12 + 26*pp**11 + 101/4*pp**10 + 301/12*pp**9 + 95/4*pp**8 + 85/4*pp**7 + 223/12*pp**6 + 33/2*pp**5 + 29/2*pp**4 + 10*pp**3 + 11/2*pp**2 + 5/2*pp + 1/2)/(pp**29 + 4*pp**28 + 8*pp**27 + 12*pp**26 + 16*pp**25 + 20*pp**24 + 24*pp**23 + 28*pp**22 + 32*pp**21 + 35*pp**20 + 36*pp**19 + 36*pp**18 + 36*pp**17 + 36*pp**16 + 36*pp**15 + 36*pp**14 + 36*pp**13 + 36*pp**12 + 36*pp**11 + 36*pp**10 + 35*pp**9 + 32*pp**8 + 28*pp**7 + 24*pp**6 + 20*pp**5 + 16*pp**4 + 12*pp**3 + 8*pp**2 + 4*pp + 1))

def check_ab(i=None):
    if i==3:
        check3()
    elif i==4:
        check4()
    elif i==5:
        check5()
    elif i==6:
        check6()
    elif i==None:
        for i in [3,4,5,6]: check_ab(i)
    else:
        raise NotImplementedError("checks only implemented for i=3,4,5,6 so far")


# expressions in the formulas (Prop 3.5) linking mu_0 and mu_1 to each other.

def mu0_term_1(g,p=pp):
    """ The first term in the expression for mu_0(g).
    """
    return sum([phi_term(phi,"proj",True,p) for phi in Phi(g+1)])

def mu0_term_2(g,p=pp):
    """ The second term in the expression for mu_0(g).
    """
    F = GF(p) if p in ZZ else None
    from gamma import Delta
    return sum([f_term(f,p) for f in Delta(2*g+2,F)])

def mu1_term(g,p=pp):
    """ The first term in the expression for mu_1(g).
    """
    return sum([phi_term(phi,"proj",False,p) for phi in Phi(2*g+2)])

def old_mu01(g,p=pp):
    """Return the pair mu_0(g), mu_1(g) by solving the linear equations
    expressing each in terms of the other and the three additional
    terms.

    if A = mu0_term_1, B = mu0_term_2, C = mu1_term

    then (Prop. 3.5)

    mu0 = (p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * (B + mu1)
    mu1 = (p^(2*g+3)-1)/(p^(2*g+3)) * C + 1/p^(2*g+3) * mu0

    so

    mu0 * (1-1/p^(4*g+6)) = (p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * B + (p^(2*g+3)-1)/(p^(4*g+6)) * C

    """
    # It is safest to make sure that these are computed at the start in the right order.
    make_betas(2*g+2,p)
    make_alphas(2*g+2, p)
    A = mu0_term_1(g,p)
    B = mu0_term_2(g,p)
    C = mu1_term(g,p)
    e = 3*g+5 if p==2 else 2*g+3
    ans0 =  ((p**(g+2)-1)/(2*p**(2*g+3)) * A + B/p**e + (p**(2*g+3)-1)/(p**(4*g+6)) * C) / (1-1/p**(4*g+6))
    ans1 =  ((p**(2*g+3)-1) * C + ans0) / p**(2*g+3)
    assert ans0 == (p**(g+2)-1)/(2*p**(2*g+3)) * A +  B/p**e + ans1/p**(2*g+3)
    return ans0, ans1

def old_mu0(g,p=pp):
    """ Return mu_0(g) for p an odd prime or generic.
    """
    return old_mu01(g,p)[0]

def old_mu1(g,p=pp):
    """ Return mu_1(g) for p an odd prime or generic.
    """
    return old_mu01(g,p)[1]

def old_rho(g,p=pp):
    """ Return rho(g) for p an odd prime or generic.  This is the local density of soluble hyperelliptic curves of genus g>=1.  The generic formula is correct for sufficiently large p:

    all p>2   for g=1;
    all p>11  for g=2;
    all p>?   for g=3, etc.
    """
    return 1 - old_mu0(g,p)

def ie(a,b): return 1-(1-a)*(1-b)

def rho_0(n,p=pp):
    """Return rho_0(n) for p an odd prime or generic, n even.  This is the
    *relative* local density of soluble y^2=f(x), restricted to primitive
    f.

    This is (a rearrangement of) Prop 3.13 of hyper.pdf.
    """
    def term(i):
        """ prob. soluble if deg(f mod p)=i
        """
        if i%2:
            return ie(beta(n-i,p), alpha(i,p))
        else:
            return (ie(beta_plus(n-i,p), alpha_plus(i,p))+ie(beta_minus(n-i,p), alpha_minus(i,p)))/2

    return (p-1)*sum([term(i)*p**i for i in range(n+1)])/p**(n+1)

def rho_1(n,p=pp):
    """Return rho_1(n) for p an odd prime or generic, n even.  This is the
    *relative* local density of soluble y^2=f(x), restricted to f with
    valuation 1.

    This different from the formula give in Prop 3.23 of hyper.pdf,
    which only involves the beta's.
    """
    def term(i):
        """ prob. soluble if deg(f/p mod p)=i
        """
        return ie(beta_0(n-i,p), alpha_0(i,p))
    # prob sol if f/p mod p is nonzero

    return (p-1)*sum([term(i)*p**i for i in range(n+1)])/p**(n+1)

# def new_AB(g,p=pp):
#     """ New formula for prob sol if f mod p is nonzero.
#     """
#     d=2*g+2
#     def term(i):
#         """ prob. soluble if deg(f mod p)=i
#         """
#         if i%2:
#             return ie(beta(d-i,p), alpha(i,p))
#         else:
#             return (ie(beta_plus(d-i,p), alpha_plus(i,p))+ie(beta_minus(d-i,p), alpha_minus(i,p)))/2
#     # prob sol if f mod p is nonzero
#     t = (p-1)*sum([term(i)*p**i for i in range(d+1)])/p**(d+1)
#     return t

# def new_C(g,p=pp):
#     """ New formula for prob sol if f is 0 mod p but not mod p^2.
#     """
#     d=2*g+2
#     def term(i):
#         """ prob. soluble if deg(f/p mod p)=i
#         """
#         return ie(beta_0(d-i,p), alpha_0(i,p))
#     # prob sol if f/p mod p is nonzero

#     return (p-1)*sum([term(i)*p**i for i in range(d+1)])/p**(d+1)

def new_AB(g,p=pp):
    """ New formula for prob sol if f mod p is nonzero.
    """
    return rho_0(2*g+2, p)

def new_C(g,p=pp):
    """ New formula for prob sol if f is 0 mod p but not mod p^2.
    """
    return rho_1(2*g+2, p)

def rho(g,p=pp):
    """Return rho(g) for p an odd prime or generic.  This is the local
    density of soluble hyperelliptic curves of genus g>=1.  The
    generic formula is correct for sufficiently large p:

    all p>2   for g=1;
    all p>11  for g=2;
    all p>?   for g=3, etc.

    """
    n = 2*g+2
    r0 = rho_0(n, p)
    r1 = rho_1(n, p)
    pn1 = p**(n+1)
    return (pn1*r0+r1)*pn1/(pn1**2-1)

def check_rho(g,p=pp):
    """Check that rho_g is correct for g=1,2 and small p.

    Here, "correct" means "agrees with Section 2" for g=1 and "agrees
    with Tom's independent calculations" for g=2.

    """
    if g==1:
        r = rho(1,p)
        rt = (8*p**10+8*p**9-4*p**8+2*p**6+p**5-2*p**4+p**3-p**2-8*p-5)/(8*(p+1)*(p**9-1))
        if r==rt:
            print("rho_1({}) OK".format(p))
        else:
            print("rho_1({}) = {} is WRONG, should be {}".format(p,r,rt))
    elif g==2:
        r = rho(2,p)
        if p==3:
            rt = 11908283690073923675989/12265526054691898243200
        elif p==5:
            rt = 21168046192107392417824270157/21315998310595527294273375000
        elif p==7:
            rt = 9225394906523129800081108647433021/9243647281033059837025942476710400
        elif p==11:
            rt = 291968807821387146869087552918410773299321/292073047488128339469598819346962539694720
        else:
            rt = (p-1)**3 * (144*p**40 + 576*p**39 + 1296*p**38 + 2232*p**37 + 3384*p**36 + 4788*p**35 + 6492*p**34 + 8263*p**33
                              + 10041*p**32 + 11580*p**31 + 12883*p**30 + 13947*p**29 + 14784*p**28 + 15378*p**27 + 15785*p**26 + 15912*p**25
                              + 15965*p**24 + 16172*p**23 + 16296*p**22 + 16337*p**21 + 16191*p**20 + 15715*p**19 + 15006*p**18 + 14095*p**17
                              + 12964*p**16 + 11580*p**15 + 9739*p**14 + 7905*p**13 + 6228*p**12 + 4662*p**11 + 3329*p**10 + 2139*p**9 + 1212*p**8
                              + 521*p**7 + 81*p**6 - 36*p**5 - 90*p**4 - 144*p**3 - 144*p**2 - 144*p - 72)/(144*p**6 *(p+1)*(p**20 -1)*(p**9 -1)*(p**7 -1))
        if r==rt:
            print("rho_2({}) OK".format(p))
        else:
            print("rho_2({}) = {} is WRONG, should be {}".format(p,r,rt))
    else:
        raise NotImplementedError("check_rho only implemented for g = 1, 2 so far")

"""
Space for comments

"""

"""
    New notation from 22/3/22

(1) alpha and beta labels switched
(2) superscripts +, -, 0 replaced by second paramater 1, u, p

"""
def alpha_1(n, p=pp):
    """
    alpha(n, 1)
    """
    return alpha_plus(n, p)

def beta_1(n, p=pp):
    """
    beta(n, 1)
    """
    return beta_plus(n, p)

def alpha_u(n, p=pp):
    """
    alpha(n, u)
    """
    return alpha_minus(n, p)

def beta_u(n, p=pp):
    """
    beta(n, u)
    """
    return beta_minus(n, p)

def alpha_p(n, p=pp):
    """
    alpha(n, p)
    """
    return alpha_0(n, p)

def beta_p(n, p=pp):
    """
    beta(n, p)
    """
    return beta_0(n, p)

def new_alpha(n, p=pp):
    """
    alpha(n, p)
    """
    return alpha(n, p)

def new_beta(n, p=pp):
    """
    beta(n, p)
    """
    return beta(n, p)

def new_rho_1(n, p=pp):
    """
    rho(n, 1)
    """
    r0 = rho_0(n,p)
    r1 = rho_1(n,p)
    pn1 = p**(n+1)
    return (pn1*r0 + r1) / (pn1 + 1)

def new_rho_p(n, p=pp):
    """
    rho(n, p)
    """
    r0 = rho_0(n,p)
    r1 = rho_1(n,p)
    pn1 = p**(n+1)
    return (pn1*r1 + r0) / (pn1 + 1)
