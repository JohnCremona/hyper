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
        return sage.all.infinity

# Initialize dicts to store the Gamma_plus/minus and Delta sets but do
#  not reset on reload.  The dicts will be initialized if they don't
#  exist (e.g. on first loading the file) or have no entries.
#  Re-initialization of the dicts is done by the initialize_dicts()
#  functions.

try:
    n = len(Gamma_plus_dict)
except NameError:
    Gamma_plus_dict = {}
try:
    n = len(Gamma_minus_dict)
except NameError:
    Gamma_minus_dict = {}

def initialize_Gamma_dicts():
    global Gamma_plus_dict, Gamma_minus_dict
    Gamma_plus_dict = {}
    Gamma_minus_dict = {}

# Initialize dicts to store the Delta sets but do not reset on reload!
try:
    nd = len(Delta_dict)
except NameError:
    Delta_dict = {}

def initialize_Delta_dicts():
    global Delta_dict
    Delta_dict = {}

# Initialize dicts to store the alphas and betas but do not reset on reload!
# The alpha and beta values for subscripts 0,1,2 are known directly.
try:
    n = len(alpha_0_dict)
except NameError:
    alpha_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(alpha_plus_dict)
except NameError:
    alpha_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1/pp}
try:
    n = len(alpha_minus_dict)
except NameError:
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

def initialize_alpha_dicts():
    global alpha_0_dict, alpha_plus_dict, alpha_minus_dict
    alpha_0_dict =      {(0,pp):0, (1,pp):1, (2,pp):1/2}
    alpha_plus_dict =   {(0,pp):1, (1,pp):1, (2,pp):1/pp}
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

try:
    n = len(beta_0_dict)
except NameError:
    beta_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(beta_plus_dict)
except NameError:
    beta_plus_dict = {(0,pp):1, (1,pp):1, (2,pp):1}
try:
    n = len(beta_minus_dict)
except NameError:
    beta_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

def initialize_beta_dicts():
    global beta_0_dict, beta_plus_dict, beta_minus_dict
    beta_0_dict =     {(0,pp):0, (1,pp):1, (2,pp):1/2}
    beta_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1}
    beta_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

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
    initialize_Gamma_dicts()
    initialize_Delta_dicts()
    initialize_N_dict()

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t(i,p)={}: {}".format(k,d[k]))

def show_alpha_dicts():
    show1dict(alpha_0_dict, "alpha_0")
    show1dict(alpha_plus_dict, "alpha_plus")
    show1dict(alpha_minus_dict, "alpha_minus")

def show_beta_dicts():
    show1dict(beta_0_dict, "beta_0")
    show1dict(beta_plus_dict, "beta_plus")
    show1dict(beta_minus_dict, "beta_minus")

def show_dicts():
    show_alpha_dicts()
    show_beta_dicts()

def N(j, p=pp):
    """The number of degree j monic irreducibles in GF(p)[X].
    """
    if not (j,p) in N_dict:
        N_dict[(j,p)] = sum([moebius(d)*p**(j//d) for d in divisors(j)]) / j
    return N_dict[(j,p)]

def Ndash(j, p=pp):
    """The number of degree j homogeneous irreducibles in GF(p)[X,Y] up to scaling.
    """
    return p+1 if j==1 else N(j,p)

def Phi(d, base=[1,1]):
    """List of factorization patterns in degree d.  Each is a list of
    pairs [d_i,e_i] with d_i*e_i summing to d, with repeats allowed
    but unordered.
    """
    if d==0:
       yield []
    d0, e0 = base
    for di in [d0..d]:
    	e1 = e0 if di==d0 else 1
	for ei in [e1..d//di]:
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

def lambda_helper(phi, NN, p=pp):
    """ Helper function for affine and projective factorization probabilities.
    """
    d = deg_fp(phi)
    return prod([prod([NN(j,p)-i for i in srange(m1(phi,j))])/prod([factorial(m2(phi,[j,i])) for i in [1..d]]) for j in [1..d]])

def lambda_A(phi, p=pp):
    """ The probability that a monic polynomial of degree deg(phi) has factorization pattern phi.
    """
    d = deg_fp(phi)
    return lambda_helper(phi, N, p) / p**d

def lambda_P(phi, p=pp):
    """ The probability that a homogeneous polynomial of degree deg(phi) has factorization pattern phi.
    """
    d = deg_fp(phi)
    return lambda_helper(phi, Ndash, p) * (p-1)/ (p**(d+1)-1)

def monics(F, d, u=1):
    """List of all degree d polynomials with leaqding coefficient u.
    """
    Fx = PolynomialRing(F,'x')
    return [Fx(v.list()+[u]) for v in F^d]

def a_nonsquare(F):
    """ The first non-square element of F (an odd finite field).
    """
    for u in F:
    	if not u.is_square():
	   return u
    raise ValueError

def no_smooth_points(f):
    """Return True iff y^2=f(x) has no smooth (affine) points over the base (odd finite) field.

    N.B.  y^2=f(x) has no smooth F_p-points if for all x in F_p either
     f(x) is nonsquare or it is 0 and x is a multiple root.

    """
    fd = f.derivative()
    return all([(not f(x).is_square()) or (f(x)==fd(x)==0)
     for x in f.base_ring()])

def Gamma_plus(d,F=None):
    """ List of monics of degree d with no smooth points.
    """
    if F==None:
       return []
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if not (q,d) in Gamma_plus_dict:
        if F in ZZ:
            F = GF(q)
        print("Computing Gamma_plus({},{})".format(d,F))
        Gamma_plus_dict[(q,d)] = [f for f in monics(F,d) if no_smooth_points(f)]
    return Gamma_plus_dict[(q,d)]

def Gamma_minus(d, F=None):
    """List of f of degree d, with (fixed) non-square leading coefficient
    u, with no smooth points but not of the form u*h^2.
    """
    if F==None:
       return []
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if not (q,d) in Gamma_minus_dict:
        if F in ZZ:
            F = GF(q)
        print("Computing Gamma_minus({},{})".format(d,F))
        u = a_nonsquare(F)
        Gamma_minus_dict[(q,d)] = [f for f in monics(F,d,u) if not (u*f).is_square() and no_smooth_points(f)]
    return Gamma_minus_dict[(q,d)]

def show_Gamma(verbose=False):
    for d,dname in zip([Gamma_plus_dict, Gamma_minus_dict], ["Gamma^+","Gamma^-"]):
        print("\n{} entries".format(dname))
        for k in sorted(d.keys()):
            if verbose:
                print("\t(p,d)={}: {}".format(k,d[k]))
            else:
                print("\t(p,d)={}: {} elements".format(k,len(d[k])))

def one_row(p):
    """ Function to check entries in Table on page 19.
    """
    F = GF(p)
    return [len(ff) for ff in [Gamma_plus(1,F),
            Gamma_plus(2,F),
            Gamma_plus(3,F),
            Gamma_minus(4,F),
            Gamma_plus(4,F),
            Gamma_plus(5,F),
            Gamma_minus(6,F),
            Gamma_plus(6,F),
            Gamma_plus(7,F),
            Gamma_minus(8,F),
            Gamma_plus(8,F)]]

def homog(F, d):
    """ List of homogeneous polynomials in F[X,Y] of degree d, up to scaling.
    """
    Fx = PolynomialRing(F,'x')
    Fxy = PolynomialRing(F,['x','y'])
    x, y = Fxy.gens()
    def homog(f):
    	return Fxy(y**d * f(x/y))
    return [homog(Fx(list(v))) for v in ProjectiveSpace(F,d)]

def is_square_homog(f):
    """ Test if f (homogeneous) is a square, by factoring.
    """
    if f.degree()%2 ==1:
       return False
    F = f.base_ring()
    f_fac = f.factor()
    return F(f_fac.unit()).is_square() and all([e%2==0 for g,e in f_fac])

def no_smooth_points_homog(f):
    """Return True iff z^2=f(x,y) has no smooth (projective) points over the base (odd finite) field.

    N.B.  z^2=f(x,y) has no smooth F_p-points if for all (x:y) in
     P^1(F_p) either f(x,y) is nonsquare or it is 0 and (x:y) is also
     a root of both derivatives.  Note that x*fx+y*fy=d*f but we must
     check that all 3 are zero to correctly handle (0:1), (1:0) and
     the case p|d.
    """
    x,y = f.parent().gens()
    fx = f.derivative(x)
    fy = f.derivative(y)
    P1 = ProjectiveSpace(f.base_ring(),1)
    return all([(not f(x,y).is_square()) or (fx(x,y)==fy(x,y)==f(x,y)==0)
     for x,y in P1])

def Delta(d,F=None):
    """Return a list of f of even degree d, homogeneous with no smooth
    points but not of the form u*h^2.  Includes scalings (the
    condition is invariant under scaling by squares).
    """
    if F==None or d%2==1 or d<6 or (d==6 and p>11):
       return []
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if not (q,d) in Delta_dict:
        if F in ZZ:
            F = GF(q)
        print("Computing Delta({},{})".format(d,F))
        u = a_nonsquare(F)
        flist = homog(F,d) # up to scaling
        # consider both f and u*f
        D1 =  [f for f in flist if not is_square_homog(u*f) and no_smooth_points_homog(f)]
        D2 =  [u*f for f in flist if not is_square_homog(f) and no_smooth_points_homog(u*f)]
        # D1+D2 is the result up to scaling by squares...
        sq = [F(a)^2 for a in [1..(q-1)//2]]
        Delta_dict[(q,d)] = flatten([[a*f for f in D1+D2] for a in sq])
    return Delta_dict[(q,d)]

def show_Delta(verbose=False):
    for k in sorted(Delta_dict.keys()):
        if verbose:
            print("(p,d)={}: {}".format(k,Delta_dict[k]))
        else:
            print("(p,d)={}: {} elements".format(k,len(Delta_dict[k])))

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

# The R() and r() functions are no longer used in the code but are
# here since they are defined in the text.  Here we instead loop over
# all roots (including infinity in the projective case) to compute the
# f_terms for f in one of the Gamma or Delta sets.

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

def affine(L,p):
    """Returns linear combination of elements of the list L of length n,
    with coefficients

    [1-1/p, 1/p-1/p^2, ..., 1/p^(n-2)-1/p^(n-1), 1/p^(n-1)].

    Works recursively according to the definition in section 3.4.
    """
    if len(L)==1:
        return L[0]
    return ((p-1)*L[0]+affine(L[1:],p))/p

def alpha_eps(eps):
    """ Return either alpha^_, alpha^0 or alpha^+ according to eps=-1,0,+1.
    """
    try:
        return [alpha_minus,alpha_0,alpha_plus][eps+1]
    except IndexError:
        return alpha

def f_term(f,p=pp):
    """Helper function for beta^+, beta^-, mu_0.  In the paper this is
    expressed differently, as a double product over j up to the degree
    and eps, with multiplicities.  Here we just take the product over
    all roots.

    Note that if there is a root of multiplicity 1 then alpha^eps(1)=1
    and the result is 0, but this will only be called with f which
    have no such roots.

    This works equally well in the projective case.
    """
    if p==pp: # will not be called in this case anyway
        return 0
    return prod([(1-alpha_eps(eps)(j,p)) for a,j,eps in signed_roots(f)])

def phi_term(phi, A_or_P, double, p, v=None):
    """Helper function for beta^0, beta^-, mu_0, mu_1.

    The first two use A_or_P="affine" to use lambda_A while the others
    use "proj" to get lambda_P.

    beta^- and mu_0 have double=True which uses alpha^-(2*e) for (1,e) in phi.

    beta^0 and mu_1 have double=False which uses alpha^0(e) for (1,e) in phi.

    """
    lam = lambda_A(phi,p) if A_or_P=="affine" else lambda_P(phi,p)
    al = (lambda i: alpha_minus(2*i,p,v)) if double else (lambda i: alpha_0(i,p,v))
    return lam * prod([1-al(e) for d,e in phi if d==1])

def beta(i,p=pp,v=None):
    """ Average of beta^+ and beta^-
    """
    return (beta_plus(i,p,v)+beta_minus(i,p,v))/2

def alpha(i,p=pp,v=None):
    """ Average of alpha^+ and alpha^-
    """
    return (alpha_plus(i,p,v)+alpha_minus(i,p,v))/2

def beta_plus(i,p=pp,v=None):
    """beta^+_i(p).

    Computed values are stored in beta_plus_dict keyed on (i,p).

    For i<3 use precomputed table.  Otherwise use recursion via
    various alphas and betas.  The internal variable v keeps track of
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
	return beta_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting beta_plus({},{})".format(i,p))
            b = beta_plus_dict[(i,p)] = 1
            return b
        pass
    F = Qp if p==pp else QQ
    v0 = "bp_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (i)
    print("Computing beta_plus({},{})".format(i,p))
    Fp = GF(p) if p in ZZ else None
    b = 1 - sum([f_term(f,p) for f in Gamma_plus(i,Fp)])/p^i

    try:
        b=F(b)
        print("setting beta_plus({},{})".format(i,p))
        beta_plus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("setting beta_plus({},{})".format(i,p))
            print("{}={}".format(v0,b))
            beta_plus_dict[(i,p)] = b
    return b

def beta_minus(i,p=pp,v=None):
    """beta^-_i(p).

    Computed values are stored in beta_minus_dict keyed on (i,p).
    """
    try:
        return beta_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting beta_minus({},{})".format(i,p))
            b = beta_minus_dict[(i,p)] = [0,1,p/(p+1)][i]
            return b
    if i%2==1:
        print("setting beta_minus({},{})".format(i,p))
        b = beta_minus_dict[(i,p)] = beta_plus(i,p,v)
        return b
    F = Qp if p==pp else QQ
    v0 = "bm_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # now i is even, use Prop 3.3(ii)
    print("Computing beta_minus({},{})".format(i,p))
    i2 = i//2
    Fp = GF(p) if p in ZZ else None
    b = 1 - sum([phi_term(phi,"affine",True,p,v) for phi in Phi(i2)]) / p^i2 - \
        sum([f_term(f,p) for f in Gamma_minus(i,Fp)]) / p^i
    try:
        b=F(b)
        print("setting beta_minus({},{})".format(i,p))
        beta_minus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("{}={}".format(v0,b))
            print("setting beta_minus({},{})".format(i,p))
            beta_minus_dict[(i,p)] = b
    return b

def beta_0(i,p=pp,v=None):
    """beta^0_i(p).

    Computed values are stored in beta_0_dict keyed on (i,p).
    """
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting beta_0({},{})".format(i,p))
            b =  beta_0_dict[(i,p)] = [0,1,1/2][i]
            return b
    F = Qp if p==pp else QQ
    v0 = "b0_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (iii)
    print("Computing beta_0({},{})".format(i,p))
    b = 1 - sum([phi_term(phi,"affine",False,p,v) for phi in Phi(i)])
    try:
        b=F(b)
        print("setting beta_0({},{})".format(i,p))
        beta_0_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("{}={}".format(v0,b))
            print("setting beta_0({},{})".format(i,p))
            beta_0_dict[(i,p)] = b
    return b

def alpha_0(i,p=pp,v=None):
    """ alpha^0_i(p).

    Computed values are stored in alpha_0_dict keyed on (i,p).
    """
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting alpha_0({},{})".format(i,p))
            a = alpha_0_dict[(i,p)] = [0,1,1/2][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "a0_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_0({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
    if i%2==0:
       blist += [beta_0(i,p,v)]
    else:
       blist += [beta(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        print("setting alpha_0({},{})".format(i,p))
        alpha_0_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            print("setting alpha_0({},{})".format(i,p))
            alpha_0_dict[(i,p)] = a
    return a

def alpha_plus(i,p=pp,v=None):
    """ alpha^+_i(p).

    Computed values are stored in alpha_plus_dict keyed on (i,p).
    """
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting alpha_plus({},{})".format(i,p))
            a = alpha_plus_dict[(i,p)] = [1,1,1/p][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "ap_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_plus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
    if i%2==0:
       blist += [beta_plus(i,p,v)]
    else:
       blist += [beta_0(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        print("setting alpha_plus({},{})".format(i,p))
        alpha_plus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            print("setting alpha_plus({},{})".format(i,p))
            alpha_plus_dict[(i,p)] = a
    return a

def alpha_minus(i,p=pp,v=None):
    """ alpha^-_i(p).

    Computed values are stored in alpha_minus_dict keyed on (i,p).
    """
    try:
        return alpha_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            print("setting alpha_minus({},{})".format(i,p))
            a = alpha_minus_dict[(i,p)] = [0,1,1/(p+1)][i]
            return a
    if i%2==1:
        print("setting alpha_minus({},{})".format(i,p))
        alpha_minus_dict[(i,p)] = alpha_plus(i,p)
        return alpha_minus_dict[(i,p)]
    F = Qp if p==pp else QQ
    v0 = "am_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_minus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
    blist += [beta_minus(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        print("setting alpha_minus({},{})".format(i,p))
        alpha_minus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            print("setting alpha_minus({},{})".format(i,p))
            alpha_minus_dict[(i,p)] = a
    return a

def make_alphas(i, p=pp, verbose=True):
    """Compute (and optionally display) all 3 alphas with subscript i
    after first computing all alphas and betas with smaller
    subscripts.
    """
    for j in [3..i-1]:
        make_alphas(j,p,False)
        make_betas(j,p,False)
    a = alpha_plus(i,p)
    if verbose:
        print("alpha_plus({},{}) = {}".format(i,p,a))
    a = alpha_minus(i,p)
    if verbose:
        print("alpha_minus({},{}) = {}".format(i,p,a))
    a = alpha_0(i,p)
    if verbose:
        print("alpha_0({},{}) = {}".format(i,p,a))

def make_betas(i, p=pp, verbose=True):
    """Compute (and optionally display) all 3 betas with subscript i
    after first computing all alphas and betas with smaller
    subscripts.
    """
    for j in [3..i-1]:
        make_alphas(j,p,False)
        make_betas(j,p,False)
    b = beta_plus(i,p)
    if verbose:
        print("beta_plus({},{}) = {}".format(i,p,b))
    b = beta_minus(i,p)
    if verbose:
        print("beta_minus({},{}) = {}".format(i,p,b))
    b = beta_0(i,p)
    if verbose:
        print("beta_0({},{}) = {}".format(i,p,b))


def check3():
    """ Check that all 3 alpha_3^eps are correct for p=3 and p generic.
    """
    a = alpha_plus(3,3)
    at = 50246/177147
    if a==at:
        print("alpha_3^+(3) OK")
    else:
        print("WRONG alpha_3^+(3) = {}, should be {}".format(a,at))

    a = alpha_minus(3,3)
    at = 50246/177147
    if a==at:
        print("alpha_3^-(3) OK")
    else:
        print("WRONG alpha_3^-(3) = {}, should be {}".format(a,at))

    a = alpha_0(3,3)
    at = 431/729
    if a==at:
        print("alpha_3^0(3) OK")
    else:
        print("WRONG alpha_3^0(3) = {}, should be {}".format(a,at))

    a = alpha_plus(3)
    at = (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8)
    if a==at:
        print("alpha_3^+(p) OK")
    else:
        print("WRONG alpha_3^+(p) = {}, should be {}".format(a,at))

    a = alpha_minus(3)
    at = (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8)
    if a==at:
        print("alpha_3^-(p) OK")
    else:
        print("WRONG alpha_3^-(p) = {}, should be {}".format(a,at))

    a = alpha_0(3)
    at = (pp**3+pp**2-2*pp+2)/(2*pp**3)
    if a==at:
        print("alpha_3^0(p) OK")
    else:
        print("WRONG alpha_3^0(p) = {}, should be {}".format(a,at))

def check4():
    """ Check that all 3 alpha_4^eps are correct for p=3, p=5 and p generic.
    """
    a = alpha_plus(4,3)
    at = 16600/59049
    if a==at:
        print("alpha_4^+(3) OK")
    else:
        print("WRONG alpha_4^+(3) = {}, should be {}".format(a,at))

    a = alpha_plus(4,5)
    at = 352624/1953125
    if a==at:
        print("alpha_4^+(5) OK")
    else:
        print("WRONG alpha_4^+(5) = {}, should be {}".format(a,at))

    a = alpha_plus(4)
    at = (pp**2+1)*(2*pp**3-pp**2-2*pp+2)/(2*pp**6)
    if a==at:
        print("alpha_4^+(p) OK")
    else:
        print("WRONG alpha_4^+(p) = {}, should be {}".format(a,at))

    a = alpha_minus(4)
    at = (2*pp**10+3*pp**9-p**5+2*pp**4-2*pp**2-3*pp-1)/(2*(pp+1)**2 *(p**9-1))
    if a==at:
        print("alpha_4^-(p) OK")
    else:
        print("WRONG alpha_4^-(p) = {}, should be {}".format(a,at))

    a = alpha_0(4)
    at = (4*pp**10+8*pp**9-4*pp**8+4*pp**6-3*pp**4+pp**3-5*pp-5)/(8*(pp+1)*(p**9-1))
    if a==at:
        print("alpha_4^0(p) OK")
    else:
        print("WRONG alpha_4^0(p) = {}, should be {}".format(a,at))

# expressions in the formulas (Prop 3.5) linking mu_0 and mu_1 to each other.

def mu0_term_1(g,p=pp):
    """ The first term in the expression for mu_0(g).
    """
    return sum([phi_term(phi,"proj",True,p) for phi in Phi(g+1)])

def mu0_term_2(g,p=pp):
    """ The second term in the expression for mu_0(g).
    """
    F = GF(p) if p in ZZ else None
    return sum([f_term(f,p) for f in Delta(2*g+2,F)])

def mu1_term(g,p=pp):
    """ The first term in the expression for mu_1(g).
    """
    return sum([phi_term(phi,"proj",False,p) for phi in Phi(2*g+2)])


def mu01(g,p=pp):
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
    make_alphas(2*g+2,p, False)
    make_betas(2*g+2, p, False)
    A = mu0_term_1(g,p)
    B = mu0_term_2(g,p)
    C = mu1_term(g,p)
    ans0 =  ((p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * B + (p^(2*g+3)-1)/(p^(4*g+6)) * C) / (1-1/p^(4*g+6))
    ans1 =  ((p^(2*g+3)-1) * C + ans0) / p^(2*g+3)
    assert ans0 == (p^(g+2)-1)/(2*p^(2*g+3)) * A +  (B + ans1) / p^(2*g+3)
    return ans0, ans1

def mu0(g,p=pp):
    """ Return mu_0(g) for p an odd prime or generic.
    """
    return mu01(g,p)[0]

def mu1(g,p=pp):
    """ Return mu_1(g) for p an odd prime or generic.
    """
    return mu01(g,p)[1]

def rho(g,p=pp):
    """ Return rho(g) for p an odd prime or generic.  This is the local density of soluble hyperelliptic curves of genus g>=1.  The generic formula is correct for sufficiently large p:

    all p>2   for g=1;
    all p>11  for g=2;
    all p>?   for g=3, etc.
    """
    return 1 - mu0(g,p)

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
All alphas and betas for i up to 6 with p=3:

alpha_0:
        (i,p)=(1, 3): 1
        (i,p)=(2, 3): 1/2
        (i,p)=(3, 3): 431/729
        (i,p)=(4, 3): 23131/39364
        (i,p)=(5, 3): 1493687989147/2541865828329
        (i,p)=(6, 3): 26377476341107224253/44887561041873369600
alpha_plus:
        (i,p)=(2, 3): 1/3
        (i,p)=(3, 3): 50246/177147
        (i,p)=(4, 3): 16600/59049
        (i,p)=(5, 3): 13670659773280445407/48630661836227715204
        (i,p)=(6, 3): 605398279518845051650813/2153584544086426253951538
alpha_minus:
        (i,p)=(2, 3): 1/4
        (i,p)=(3, 3): 50246/177147
        (i,p)=(4, 3): 88519/314912
        (i,p)=(5, 3): 13670659773280445407/48630661836227715204
        (i,p)=(6, 3): 27339928051320364957/97256382257392300800

beta_0:
        (i,p)=(0, 3): 0
        (i,p)=(1, 3): 1
        (i,p)=(2, 3): 1/2
        (i,p)=(3, 3): 4319/6561
        (i,p)=(4, 3): 6137/9841
        (i,p)=(5, 3): 129514464056263/205891132094649
        (i,p)=(6, 3): 690037935950003/1098030248972800
beta_plus:
        (i,p)=(0, 3): 1
        (i,p)=(1, 3): 1
        (i,p)=(2, 3): 1
        (i,p)=(3, 3): 26/27
        (i,p)=(4, 3): 76/81
        (i,p)=(5, 3): 160260073/172186884
        (i,p)=(6, 3): 28366779023771/30502389939948
beta_minus:
        (i,p)=(0, 3): 0
        (i,p)=(1, 3): 1
        (i,p)=(2, 3): 3/4
        (i,p)=(3, 3): 26/27
        (i,p)=(4, 3): 288303/314912
        (i,p)=(5, 3): 160260073/172186884
        (i,p)=(6, 3): 9541669997405587/10262359634630400

sage: A = mu0_term_1(2,3); A
681602664875234210093/972563822573923008000
sage: B = mu0_term_2(2,3); B
0
sage: C = mu1_term(2,3); C
42621034619903398115111/159451838710994677161600

sage: m0_2_3 = mu0(2,3); m0_2_3
86819540747429135587217/6709242751916468339030400
sage: m1_2_3 = mu1(2,3); m1_2_3
7767853960143613115031503/29073385258304696135798400

sage: m0_2_3 == ((3^4-1)/(2*3^7))*A + (B+m1_2_3)/3^7
True
sage: m1_2_3 == ((3^7-1)/3^7)*C + m0_2_3/3^7
True
sage: rho_2_3 = 1-m0_2_3; rho2_2_3
6622423211169039203443183/6709242751916468339030400


"""

