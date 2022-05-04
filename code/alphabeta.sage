from sage.all import (save, load, prod, polygen, xmrange_iter, moebius, primes, Infinity)
from sage.all import (QQ, ZZ, GF, PolynomialRing, ProjectiveSpace)

from basics import (Qp, pp, affine)

################################# Set up dicts for Gamma sets  ##################################

# The short version of Gamma_plus, Gamma_minus with keys (p,d) only
# exist for p not dividing d and hold a restricted set of
# "affine-reduced" polynomials with leading coefficients restricted to
# (1,0,{0,1,u},...)         for d even or p=3(4)
# (1,0,{0,1,u,u^2,u^3},...) for d odd and p=1(4)
#
# each being a representative of an affine orbit. of size p or p(p-1)/2 or p(p-1)/4.

try:
    n = len(Gamma_plus_dict)
except NameError:
    Gamma_plus_dict = {}
try:
    n = len(Gamma_minus_dict)
except NameError:
    Gamma_minus_dict = {}
try:
    n = len(Gamma_plus_short_dict)
except NameError:
    Gamma_plus_short_dict = {}
try:
    n = len(Gamma_minus_short_dict)
except NameError:
    Gamma_minus_short_dict = {}

try:
    n = len(Gamma_plus_mult_dict)
except NameError:
    Gamma_plus_mult_dict = {}
try:
    n = len(Gamma_minus_mult_dict)
except NameError:
    Gamma_minus_mult_dict = {}
try:
    n = len(Gamma_plus_short_mult_dict)
except NameError:
    Gamma_plus_short_mult_dict = {}
try:
    n = len(Gamma_minus_short_mult_dict)
except NameError:
    Gamma_minus_short_mult_dict = {}


max_p_for_degree = {1:0, 2:0, 3:3, 4:5, 5:11, 6:13, 7:19, 8:23, 9:37, 10:37}

def initialize_Gamma_dicts():
    global Gamma_plus_dict, Gamma_minus_dict, Gamma_plus_short_dict, Gamma_minus_short_dict
    Gamma_plus_dict = {}
    Gamma_minus_dict = {}
    Gamma_plus_short_dict = {}
    Gamma_minus_short_dict = {}

def initialize_Gamma_mult_dicts():
    global Gamma_plus_mult_dict, Gamma_minus_mult_dict, Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict
    Gamma_plus_mult_dict = {}
    Gamma_minus_mult_dict = {}
    Gamma_plus_short_mult_dict = {}
    Gamma_minus_short_mult_dict = {}

def save_Gammas_old():
    filename="Gamma"
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict, Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict],
                             ["plus", "minus", "plus_short_mult", "minus_short_mult"]):
        for k in Gdict.keys():
            p = k[0]
            if p==2:
                Gdict[k] = [[[int(c) for c in pol.coefficients(sparse=False)] for pol in fh] for fh in Gdict[k]]
        f = "_".join([filename, suffix])
        print("Saving {}".format(f))
        save(Gdict, f)
        for k in Gdict.keys():
            p = k[0]
            if p==2:
                Fx = PolynomialRing(GF(p), 'x')
                Gdict[k] = [[Fx(co1) for co1 in co] for co in Gdict[k]]

def save_Gammas():
    filename="Gamma"
    for Gdict, suffix in zip([Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict],
                             ["plus_short_mult", "minus_short_mult"]):
        f = "_".join([filename, suffix])
        print("Saving {}".format(f))
        save(Gdict, f)

# The restore functions use the update() method so that local values
# are preserved, but NB if the same key exists locally and on file
# then the file version will overwrite the local one.

def restore_Gammas_old(filename="Gamma"):
    global Gamma_plus_dict, Gamma_minus_dict, Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict, Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict],
                             ["plus", "minus", "plus_short_mult", "minus_short_mult"]):
        f = "_".join([filename, suffix])
        print("Restoring {}".format(f))
        Gdict.update(load(f))
        if suffix in ["plus", "minus"]:
            for k in Gdict.keys():
                p = k[0]
                if p==2:
                    Fx = PolynomialRing(GF(p), 'x')
                    Gdict[k] = [[Fx(co1) for co1 in co] for co in Gdict[k]]

def restore_Gammas(filename="Gamma"):
    global Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict
    for Gdict, suffix in zip([Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict],
                             ["plus_short_mult", "minus_short_mult"]):
        f = "_".join([filename, suffix])
        print("Restoring {}".format(f))
        Gdict.update(load(f))

################################# Set up dicts for alphas and betas  ##################################

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
    #initialize_Delta_dicts()
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

def N(j, p=pp):
    """The number of degree j monic irreducibles in GF(p)[X].
    """
    global N_dict
    if not (j,p) in N_dict:
        N_dict[(j,p)] = sum([moebius(d)*p**(j//d) for d in ZZ(j).divisors()]) / j
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

def lambda_helper(phi, NN, p=pp):
    """ Helper function for affine and projective factorization probabilities.
    """
    d = deg_fp(phi)
    return prod([prod([NN(j,p)-i for i in
                       range(m1(phi,j))])/prod([ZZ(m2(phi,[j,i])).factorial()
                                                for i in range(1,d+1)]) for j in range(1,d+1)])

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

def a_nonsquare(F):
    """ The first non-square element of F (an odd finite field).
    """
    for u in F:
        if not u.is_square():
           return u
    raise ValueError("Field {} has no non-squares!".format(F))

def no_smooth_points(f): 
    """Return True iff y^2=f(x) has no smooth
    (affine) points over the base (odd finite) field.

    N.B.  y^2=f(x) has no smooth F_p-points if for all x in F_p either
     f(x) is nonsquare or it is 0 and x is a multiple root.
    """
    fd = f.derivative()
    return all([(not f(x).is_square()) or (f(x)==fd(x)==0)
     for x in f.base_ring()])

def smooth_points_mod2(f,h):
    """ Return a list of the smooth affine points on z^2+h(x)z=f(x).
    """ 
    if f.parent().ngens()==1:
        # NB even in char. 2, f'(0) gives the coefficient of x
        pts = []
        fd=f.derivative()
        hd=h.derivative()
        if f(0)==0 and (fd(0),h(0))!=(0,0):
           pts += [[0,0]]
        if f(1)==0 and (fd(1),h(1))!=(0,0):
           pts += [[1,0]]
        if f(0)!=h(0) and (fd(0)-hd(0),h(0))!=(0,0):
           pts += [[0,1]]
        if f(1)!=h(1) and (fd(1)-hd(1),h(1))!=(0,0):
           pts += [[1,1]]
        return pts
    # homogeneous case
    R1 = PolynomialRing(f.base_ring(),'x')
    x = R1.gen()
    f1 = f([x,1])
    h1 = h([x,1])
    # first affine points, with y=1:
    pts = [[P[0],1,P[1]] for P in smooth_points_mod2(f1,h1)]
    # next, points of the form [1,0,z].  NB cannot have x=y=0.
    x,y = f.parent().gens()
    fy = f.derivative(y)
    hy = h.derivative(y)
    if f(1,0)==0 and (fy(1,0),h(1,0))!=(0,0):
       pts += [[1,0,0]]
    if f(1,0)!=h(1,0) and (fy(1,0)+hy(1,0),h(1,0))!=(0,0):
       pts += [[1,0,1]]
    return pts

def all_points_mod2(f,h):
    return [P for P in ProjectiveSpace(GF(2),2) if P[2]*(P[2]+h(P[:2]))==f(P[:2])]

def no_smooth_points_mod2(f,h):
    """Return True iff z^2+h(x)z=f(x) has no smooth  points over F_2
    """
    return len(smooth_points_mod2(f,h))==0

def nfactors_mod2(f,h,abs=False):
    """Return list of multiplicities of irreducible factors of z^2+h*z-f
    over GF(2), or over GF(4) if abs=True.  This will be [1] if
    irreducible, [2] if a square and [1,1] if split.
    """
    F = f.base_ring() # GF(2)
    if abs:
        F = GF(F.cardinality()**2,'a') # GF(4)
    if f.parent().ngens()==1: # inhomogeneous case: f,h in GF(2)[x]
        R2 = PolynomialRing(F,2, ['x','z'])
        x, z = R2.gens()
    else:
        # homogeneous case:  f,h in GF(2)[x,y]
        R3 = PolynomialRing(F,3,['x','y','z'])
        x, y, z = R3.gens()
    return [c[1] for c in (z^2+h*z-f).factor()]

def is_irred_mod2(f,h,abs=False):
    return nfactors_mod2(f,h,abs)==[1]

def Gamma_plus_mults(d,p):
    """Counter giving frequencies of each pattern of signed root
    multiplicities for f in Gamma(d,1; p)
    """
    if (p,d) in Gamma_plus_short_mult_dict:
        return Gamma_plus_short_mult_dict[(p,d)]
    raise RuntimeError("No stored Gamma_plus multiplicities for degree {}, p={}".format(d,p))

def Gamma_minus_mults(d,p):
    """Counter giving frequencies of each pattern of signed root
    multiplicities for f in Gamma(d,u; p)
    """
    if (p,d) in Gamma_minus_short_mult_dict:
        return Gamma_minus_short_mult_dict[(p,d)]
    raise RuntimeError("No stored Gamma_minus multiplicities for degree {}, p={}".format(d,p))

def Gamma_plus(d,F=None):
    """List of monics of degree d with no smooth points, with multiplicity
    flag (set when retrieved from the precomputed restricted list,
    else not set).
    """
    if F==None:
       return [], False
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if q>max_p_for_degree.get(d, Infinity):
        return [], False
    if (q,d) in Gamma_plus_short_dict:
        return Gamma_plus_short_dict[(q,d)], True
    if (q,d) in Gamma_plus_dict:
        return Gamma_plus_dict[(q,d)], False
    if F in ZZ:
        F = GF(q)
    print("Computing Gamma_plus({},{})".format(d,F))
    if q==2:
        from basics import monics
        res = [[f,h] for f in monics(F,d,d%2)
               for h in monics(F,(d+1)//2,(d+1)%2)
               if no_smooth_points_mod2(f,h)]
    else:
        res = Gamma_new(d,F,+1)
    Gamma_plus_dict[(q,d)] = res
    #print("accessing Gamma(d,1) with p={}".format(d,q))
    return res, False

def Gamma_default(d,F,plusorminus):
    if plusorminus==+1:
       return Gamma_plus_default(d,F)
    else:
       return Gamma_minus_default(d,F)

def Gamma_plus_default(d,F):
    p = F.cardinality()
    from basics import monics, monics0
    m = monics if d%p==0 else monics0
    res = [f for f in m(F,d) if no_smooth_points(f)]
    if d%p==0:
       return res
    x = res[0].parent().gen()
    return [f(x+b) for b in F for f in res]

def Gamma_minus_default(d,F):
    p = F.cardinality()
    u = a_nonsquare(F)
    from basics import monics, monics0
    m = monics if d%p==0 else monics0
    res = [f for f in m(F,d,u) if (not (u*f).is_square()) and no_smooth_points(f)]
    if d%p==0:
       return res
    x = res[0].parent().gen()
    return [f(x+b) for b in F for f in res]

def Gamma_new(d,F,plusorminus):
    if d<3: return []
    if d<4 and F.cardinality()>3: return []
    if d<5 and F.cardinality()>5: return []
    if d<6 and F.cardinality()>11: return []
    if d<7 and F.cardinality()>20: return []
    if d%2==0:
       return Gamma_new_even(d,F,plusorminus)
    else:
       return Gamma_new_odd(d,F,plusorminus)

def Gamma_new_even(d,F,plusorminus):
    p = F.cardinality()
    if p<=d-3 or d<=3 or p.divides(d):
       return Gamma_default(d,F,plusorminus)
    x = polygen(F)
    ff0 = prod([x-j for j in range(d-2)])
    ff  = [f//f(k) for k,f in enumerate([ff0//(x-k) for k in range(d-2)])]
    assert all([ff[i](j)==F(i==j) for i in range(d-2) for j in range(d-2)])
    # list of 0 and non-squares:
    ns = [i for i in F if i.is_zero() or not i.is_square()]
    p2 = (p+1)//2
    assert len(ns) == p2
    rr = range(1,p2)
    u = ns[1] # first non-square
    s = ff0[d-3]
    t = ff0[d-4]-s**2
    if plusorminus==-1:
       t*=u
       u1=u
       test = lambda f: no_smooth_points(f) and not (u*f).is_square()
    else:
       u1=1
       test = lambda f: no_smooth_points(f)

    def pols(k):
        """Construct polys of degree d with top 3 coeffs 1,0,k and d-2 non-square values
        """
        #print("k={}".format(k))
        temp = [(u1*x**2-s*u1*x+k-t)*ff0 + sum([w[j]*ff[j] for j in range(d-2)])
           for w in xmrange_iter([ns for _ in range(d-2)])]
        assert all([list(f)[-3:] == [k,0,u1] for f in temp])
        temp = [f for f in temp if test(f)]
        if k:
           temp = [f(r*x)/r**d for r in rr for f in temp]
        return temp

    return [f(x+b) for f in sum([pols(k) for k in [0,1,u]],[]) for b in F]

def Gamma_new_odd(d,F,plusorminus):
    p = F.cardinality()
    if p<d or d<=2 or p.divides(d):
       return Gamma_plus_default(d,F)
    x = polygen(F)
    ff0 = prod([x-j for j in range(d-1)])
    ff  = [f//f(k) for k,f in enumerate([ff0//(x-k) for k in range(d-1)])]
    ff0 *= (x+sum(range(d-1)))
    assert all([ff[i](j)==F(i==j) for i in range(d-1) for j in range(d-1)])
    # list of 0 and non-squares:
    ns = [i for i in F if i.is_zero() or not i.is_square()]
    p2 = (p+1)//2
    assert len(ns) == p2
    u = ns[1] # first non-square
    if plusorminus==-1:
       u1=u
       test = lambda f: no_smooth_points(f) and not (u*f).is_square()
    else:
       u1=1
       test = lambda f: no_smooth_points(f)

    # Construct polys of degree d with top 2 coeffs 0,k and d-1 non-square values
    temp = [u1*ff0 + sum([w[j]*ff[j] for j in range(d-1)])
           for w in xmrange_iter([ns for _ in range(d-1)])]
    assert all([list(f)[-2:] == [0,u1] for f in temp])
    temp = [f for f in temp if test(f)]

    return [f(x+b) for f in temp for b in F]

def Gamma_minus(d, F=None):
    """List of f of degree d, with (fixed) non-square leading coefficient
    u, with no smooth points but not of the form u*h^2, with
    multiplicity flag (set when retrieved from the precomputed
    restricted list, else not set).
    """
    if F==None:
       return [], False
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if q>max_p_for_degree.get(d, Infinity):
        return [], False
    if (q,d) in Gamma_minus_short_dict:
        return Gamma_minus_short_dict[(q,d)], True
    if (q,d) in Gamma_minus_dict:
        return Gamma_minus_dict[(q,d)], False
    if d%2:
        res, fl = Gamma_plus(d,F)
        Gamma_minus_dict[(q,d)] = res
        return res, False
    if F in ZZ:
        F = GF(q)
    print("Computing Gamma_minus({},{})".format(d,F))
    if q==2:
        from basics import monics
        res = [[f,h] for f in monics(F,d,1)
               for h in monics(F,d//2,1)
            if no_smooth_points_mod2(f,h) and is_irred_mod2(f,h,True)]
    else:
        res = Gamma_new(d,F,-1)
    Gamma_minus_dict[(q,d)] = res
    #print("accessing Gamma(d,u) with p={}".format(d,q))
    return res, False

def show_Gamma(verbose=False):
    for d,dname in zip([Gamma_plus_dict, Gamma_minus_dict, Gamma_plus_short_mult_dict, Gamma_minus_short_mult_dict], ["Gamma(n,1)","Gamma(n,u)", "Gamma(n,1) mod affine multiplicities", "Gamma(n,u) mod affine multiplicities"]):
        print("\n{} entries".format(dname))
        for k in sorted(d.keys()):
            if verbose:
                print("\t(p,d)={}: {}".format(k,d[k]))
            else:
                print("\t(p,d)={}: {} elements".format(k,len(d[k])))

def one_row(p):
    """ Function to check entries in Table in paper
    """
    from basics import f_multiplicity
    F = GF(p)
    table = {}
    table[3] = [0, 0, 1, 0, 6, 21, 37, 64, 192, 495, 576]
    table[5] = [0, 0, 0, 0, 5, 47, 145, 250, 1285, 5820, 6440]
    table[7] = [0, 0, 0, 0, 0, 49, 196, 392, 2992, 18928, 21126]
    table[11] = [0, 0, 0, 0, 0, 11, 55, 220, 3762, 35442, 43032]
    table[13] = [0, 0, 0, 0, 0, 0, 0, 104, 2691, 29471, 38064]
    table[17] = [0, 0, 0, 0, 0, 0, 0, 0, 816, 10404, 15810]
    table[19] = [0, 0, 0, 0, 0, 0, 0, 0, 171, 5130, 8436]
    table[23] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 506, 1012]
    table[29] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    table[31] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

    d_list = [1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8]
    Gamma_list = [Gamma_plus if i in [0,1,2,4,5,7,8,10] else Gamma_minus for i in range(11)]
    def count_f(flist_mflag):
        flist, mflag = flist_mflag
        return sum(f_multiplicity(f) for f in flist) if mflag else len(flist)
    res = [count_f(G(d,F)) for d,G in zip(d_list, Gamma_list)]
    if p in table:
       if res==table[p]:
          print("p={} OK".format(p))
       else:
          print("p={} not OK, table is\n{} but we get\n{}".format(p,table[p],res))
    return res

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

def beta_eps(eps):
    """ Return the function beta(-,u), beta(-,p) or beta(-,1) according to eps=-1,0,+1.
    """
    try:
        return [beta_minus,beta_0,beta_plus][eps+1]
    except IndexError:
        return beta

def f_term(f,p=pp):
    """Helper function for alpha(-,eps).  In the paper this is
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
    from basics import signed_roots
    return prod((1-beta_eps(eps)(j,p)) for a,j,eps in signed_roots(f))

def sum_f_terms(flist, p=pp, mflag=False):
    """
    Sum of f_term(f,p) over f in flist
    """
    if p==pp: # will not be called in this case anyway
        return 0
    if mflag:
        from basics import f_multiplicity
        return sum(f_multiplicity(f)*f_term(f, p) for f in flist)
    else:
        return sum(f_term(f, p) for f in flist)

def sum_f_terms_from_mults(counts_dict, p=pp):
    return sum(cnt*prod(1-beta_eps(eps)(j,p) for j,eps in mlt) for mlt, cnt in counts_dict.items())

def fh_term(f,h):
    """Helper function for alpha(-,eps) in case p=2.  In the paper
    this is expressed differently, as a double product over j up to
    the degree and eps, with multiplicities.  Here we just take the
    product over all roots.

    Note that if there is a root of multiplicity 1 then beta(1,eps)=1
    and the result is 0, but this will only be called with f which
    have no such roots.

    This works equally well in the projective case.

    """
    from basics import point_multiplicities
    return prod([(1-beta_eps(eps)(j,2)) for P,(j,eps) in point_multiplicities(f,h)])

def sum_fh_terms(fhlist):
    """
    Sum of fh_term(f,h) over (f,h) in fhlist
    """
    return sum(fh_term(f,h) for f,h in fhlist)

def phi_term(phi, double, p, v=None):
    """Helper function for alpha(-,p), alpha(-,u).

    alpha(-,u) has double=True which uses beta(2*e,u) for (1,e) in phi.

    alpha(-,p) has double=False which uses beta(e,p) for (1,e) in phi.

    """
    be = (lambda i: beta_minus(2*i,p,v)) if double else (lambda i: beta_0(i,p,v))
    return lambda_A(phi,p) * prod(1-be(e) for d,e in phi if d==1)

def sum_phi_terms(i, double, p, v):
    j = i//2 if double else i
    return sum(phi_term(phi, double, p, v) for phi in Phi(j))

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
    global alpha_plus_dict
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_plus({},{})".format(i,p))
            a = alpha_plus_dict[(i,p)] = 1
            return a
        pass
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "ap_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose: print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (i)
    if verbose: print("Computing alpha_plus({},{})".format(i,p))
    if p in ZZ:
        e = ((3*i+1)//2 if i%2 else 3*i//2) if p==2 else i
        a = 1 - sum_f_terms_from_mults(Gamma_plus_mults(i,p), p)/p**e
    else:
        a = 1
    try:
        a = F(a)
        if verbose: print("setting alpha_plus({},{})".format(i,p))
        alpha_plus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("setting alpha_plus({},{})".format(i,p))
                print("{}={}".format(v0,a))
            alpha_plus_dict[(i,p)] = a
    return a

def alpha_minus(i,p=pp,v=None, verbose=False):
    """alpha(i,u; p).

    Computed values are stored in alpha_minus_dict keyed on (i,p).
    """
    global alpha_minus_dict
    try:
        return alpha_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_minus({},{})".format(i,p))
            a = alpha_minus_dict[(i,p)] = [0,1,p/(p+1)][i]
            return a
    if i%2==1:
        if verbose: print("setting alpha_minus({},{})".format(i,p))
        a = alpha_minus_dict[(i,p)] = alpha_plus(i,p,v)
        return a
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "am_{}_{}".format(i,p)
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
    a = 1 - sum_phi_terms(i,True,p,v) / p**i2
    if p in ZZ:
        e = 3*i2 if p==2 else i
        a = a - sum_f_terms_from_mults(Gamma_minus_mults(i, p),p) / p**e
    try:
        a = F(a)
        if verbose: print("setting alpha_minus({},{})".format(i,p))
        alpha_minus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting alpha_minus({},{})".format(i,p))
            alpha_minus_dict[(i,p)] = a
    return a

def alpha_0(i,p=pp,v=None, verbose=False):
    """alpha(i,p; p).

    Computed values are stored in alpha_0_dict keyed on (i,p).
    """
    global alpha_0_dict
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose:
                print("setting alpha_0({},{})".format(i,p))
            a = [0,1,1/2][i]
            alpha_0_dict[(i,p)] = a
            return a
    make_alphas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "a0_{}_{}".format(i,p)
    if v==None:
        v=v0
        if verbose:
            print("Setting "+v0)
    else:
        if v==v0:
            if verbose: print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (iii)
    if verbose:
        print("Computing alpha_0({},{})".format(i,p))
    a = 1 - sum_phi_terms(i,False,p,v)
    try:
        a = F(a)
        if verbose:
            print("setting alpha_0({},{})".format(i,p))
        alpha_0_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose:
            print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting alpha_0({},{})".format(i,p))
            alpha_0_dict[(i,p)] = a
    return a

def beta_0(i,p=pp,v=None, verbose=False):
    """ beta(i,p; p).

    Computed values are stored in beta_0_dict keyed on (i,p).
    """
    global beta_0_dict
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_0({},{})".format(i,p))
            a = beta_0_dict[(i,p)] = [0,1,1/2][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "b0_{}_{}".format(i,p)
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
    b = affine(blist,p)
    try:
        b = F(b)
        if verbose: print("setting beta_0({},{})".format(i,p))
        beta_0_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("{}={}".format(v0,b))
                print("setting beta_0({},{})".format(i,p))
            beta_0_dict[(i,p)] = b
    return b

def beta_plus(i,p=pp,v=None, verbose=False):
    """ beta(i,1; p).

    Computed values are stored in beta_plus_dict keyed on (i,p).
    """
    global beta_plus_dict
    try:
        return beta_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_plus({},{})".format(i,p))
            b = beta_plus_dict[(i,p)] = [1,1,1/p][i]
            return b
    make_betas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "bp_{}_{}".format(i,p)
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
    b = affine(blist,p)
    try:
        b = F(b)
        if verbose: print("setting beta_plus({},{})".format(i,p))
        beta_plus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("{}={}".format(v0,b))
                print("setting beta_plus({},{})".format(i,p))
            beta_plus_dict[(i,p)] = b
    return b

def beta_minus(i,p=pp,v=None, verbose=False):
    """ beta(i,u; p).

    Computed values are stored in beta_minus_dict keyed on (i,p).
    """
    global beta_minus_dict
    try:
        return beta_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_minus({},{})".format(i,p))
            b = beta_minus_dict[(i,p)] = [0,1,1/(p+1)][i]
            return b
    if i%2==1:
        if verbose: print("setting beta_minus({},{})".format(i,p))
        beta_minus_dict[(i,p)] = beta_plus(i,p)
        return beta_minus_dict[(i,p)]
    make_betas(i-1,p)
    F = Qp if p==pp else QQ
    v0 = "bm_{}_{}".format(i,p)
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
    b = affine(blist,p)
    try:
        b = F(b)
        if verbose: print("setting beta_minus({},{})".format(i,p))
        beta_minus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("{}={}".format(v0,b))
                print("setting beta_minus({},{})".format(i,p))
            beta_minus_dict[(i,p)] = b
    return b

def make_betas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 betas with subscript i
    after first computing all betas and alphas with smaller
    subscripts.
    """
    if (i,p) in beta_plus_dict and (i,p) in beta_minus_dict and (i,p) not in beta_0_dict:
        return
    if verbose:
        print("Making all beta({}, eps; {})".format(i,p))
    for j in range(3,i):
        make_betas(j,p)
        make_alphas(j,p)
    b = beta_plus(i,p)
    if verbose:
        print("beta({},1; {}) = {}".format(i,p,b))
    b = beta_minus(i,p)
    if verbose:
        print("beta({},u; {}) = {}".format(i,p,b))
    b = beta_0(i,p)
    if verbose:
        print("beta({},p; {}) = {}".format(i,p,b))

def make_alphas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 alphas with subscript i
    after first computing all betas and alphas with smaller
    subscripts.
    """
    if (i,p) in alpha_plus_dict and (i,p) in alpha_minus_dict and (i,p) in alpha_0_dict:
        return
    if verbose:
        print("Making all alpha({}, eps; {})".format(i,p))
    for j in range(3,i):
        make_betas(j,p)
        make_alphas(j,p)
    a = alpha_plus(i,p)
    if verbose:
        print("alpha({},1; {}) = {}".format(i,p,a))
    a = alpha_minus(i,p)
    if verbose:
        print("alpha({},u; {}) = {}".format(i,p,a))
    a = alpha_0(i,p)
    if verbose:
        print("alpha({},p; {}) = {}".format(i,p,a))

def check_value(ab,i,eps,val,p=pp):
    myval = [beta_minus,beta_0,beta_plus][eps+1](i,p) if ab=="beta" else [alpha_minus,alpha_0,alpha_plus][eps+1](i,p)
    sup = ["u","p","1"][eps+1]
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

def rho(g,p=pp):
    """Return rho(g) for p an odd prime or generic.  This is the local
    density of soluble hyperelliptic curves of genus g>=1.  The
    generic formula is correct for sufficiently large p:

    all p>2   for g=1;
    all p>11  for g=2;
    all p>29   for g=3, etc.

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

################ Code to create Gamma sets from the C program output ##############################

"""
For n even output lines look like

13 u [1,0,0,0,0,0,0,0,10,0,12]
13 1 [1,0,0,12,0,0,0,1,4,8,11]
or
13 1 [1,0,1,6,0,0,0,0,8,7,5]
13 u [1,0,1,6,0,0,0,4,2,10,12]
or
13 u [1,0,2,6,0,0,0,8,8,9,9]
13 1 [1,0,2,11,0,0,0,11,6,0,6]

with a list of coefficients *starting with the leading coefficient 1*
of a monic polynomial f(x) in Gamma(10,u; 13) or Gamma(10,1; 13). The
first coefficients are 1,0 c with c in {0,1,u} (so u=2 in the
example).

To get the full list of Gamma(n,1; p) or Gamma(n,u; p) take lines starting
"p 1 " or "p u " respectively, and:

 - take the f starting [1,0,0,...] and collect all f(x+b) for b in F_p, i.e. 0<=b<=p-1.

 - take the f starting [1,0,c,...] with c!=0 and collect all
   f(a*x+b)/a^n for a in F_p^* up to sign, b in F_p, i.e. (a,b) with
   1<=a<=(p-1)/2 and 0<=b<=p-1/

For n odd (e.g. n=9) output lines look like

13 u [1,0,0,1,0,0,0,0,0,10]
13 1 [1,0,0,8,0,0,0,0,0,11]
or
13 1 [1,0,1,1,0,10,4,11,2,7]
13 u [1,0,1,9,5,5,10,3,6,3]
or
13 u [1,0,2,7,12,10,11,6,0,0]
13 1 [1,0,2,7,12,11,3,0,4,6]

as before.

To get the full set Gamma(n,1; p) the procedure depends on p mod 4.
If p=3 (mod 4), so that all squares a 4th powers, proceed exactly as
for n even, using only lines starting "p 1 ".  When p=1 (mod 4), we
need to take consider lines starting "p 1 " and "p u ".  For a "p 1 "
line and f starting [1,0,0,...] just apply p translations as before.
For a "p 1 "line and f starting [1,0,c,...] with c!=0, apply affine
transforms (a,b) with a *square* and up to sign.  For a "p u " line
and f starting [1,0,c,...] with c!=0, apply affine transforms (a,b)
with a *non-square* and up to sign.  Ignore "p u " lines starting
[1,0,0,...].

"""

def read_gamma_c_output(n, p, u, fname):
    """Read an output file from running gamma$n.c on prime p.  Ignore the
    last three lines which start "Checked" or "#".  All other lines
    are as above, where the coefficient list has length n+1.

    Returns two lists list_1 and list_u of the coefficient lists
    starting "p 1 " and "p u " respectively.  The parameters n,p,u are
    just for consistency checks, u being the least quadratic
    nonresidue mod p.
    """
    list_1 = []
    list_u = []
    if n<3 or p>max_p_for_degree.get(n,Infinity):
        return list_1, list_u
    with open(fname) as infile:
        for L in infile:
            if L[0] in ["C", "#", "p"]:
               #print("ignoring line '{}'".format(L.strip()))
               continue
            pp, c, coeffs = L.split()
            assert int(pp)==p
            assert c in ["1", "u"]
            coeffs = [int(a) for a in coeffs[1:-1].split(",")]
            assert len(coeffs)==n+1
            assert coeffs[0]==1
            if n%p:
                assert coeffs[1]==0
                assert coeffs[2] in [0,1,u]
            else:
                assert coeffs[1] in [0,1]
            coeffs.reverse()
            (list_1 if c=="1" else list_u).append(coeffs)
    return list_1, list_u

def read_gamma_c_output_iter(n, p, u, fname, code="1"):
    """Read an output file from running gamma$n.c on prime p.  Ignore the
    last three lines which start "Checked" or "#".  All other lines
    are as above, where the coefficient list has length n+1.

    Returns an iterator through the coefficient lists of the lines
    starting "p 1 " (if code=="1") and "p u " (if code=="1")
    respectively.  The parameters n,p,u are just for consistency
    checks, u being the least quadratic nonresidue mod p.

    """
    with open(fname) as infile:
        for L in infile:
            if L[0] in ["C", "#", "p"]:
               #print("ignoring line '{}'".format(L.strip()))
               continue
            pp, c, coeffs = L.split()
            assert int(pp)==p
            assert c in ["1", "u"]
            if not c==code:
                continue
            coeffs = [int(a) for a in coeffs[1:-1].split(",")]
            assert len(coeffs)==n+1
            assert coeffs[0]==1
            if n%p:
                assert coeffs[1]==0
                assert coeffs[2] in [0,1,u]
            else:
                assert coeffs[1] in [0,1]
            coeffs.reverse()
            yield coeffs

def scale(f,a):
    """
    Given f(x) monic in F[x] and a nonzero in F, return the monic f(a*x)/a^deg(f)
    """
    x = f.parent().gen()
    return f(a*x)/a**f.degree()

def x_shift(f,b):
    """
    Given f(x) monic in F[x] and b in F, return the monic f(x+b)
    """
    x = f.parent().gen()
    return f(x+b)

def affine_transform(f,a,b):
    """
    Given f(x) monic in F[x] and a,b in F with a nonzero, return the monic f(a*(x+b))/a^deg(f)
    """
    return x_shift(scale(f,a),b)

def expand1(f, alist):
    """
    for f(x) monic in F[x] with next coefficient 0, return all affine (a,b)-transforms with a in alist
    """
    p = f.base_ring().cardinality()
    if f[f.degree()-2]==0:
        return [x_shift(f,b) for b in range(p)]
    else:
        return [affine_transform(f,a,b) for a in alist for b in range(p)]

def expand2(f, alist):
    """
    for f(x) monic in F[x], return all a-scalings a in alist
    """
    if f[f.degree()-1]==0:
        return [f]
    else:
        return [scale(f,a) for a in alist]

def make_gammas_even(n,p, restricted=False):
    """Read from file "gamma{n}_{p}.out" and return the complete sets
    Gamma(n,1), Gamma(n,u), for n even (when restricted=False), or
    just the reduced ones when restricted=True.

    Restricted means f = x^n+0*x^{n-1}+c*x^{n-2}+... with c in
    {0,1,u}, representing an affine orbit of size p, p(p-1)/1,
    p(p-1)/2 respectively.

    """
    assert n%2==0
    F = GF(p)
    Fx = PolynomialRing(F, 'x')
    u = a_nonsquare(F)
    l1, lu = read_gamma_c_output(n, p, u, "gamma{}_{}.out".format(n,p))
    l1 = [Fx(coeffs) for coeffs in l1]
    lu = [Fx(coeffs) for coeffs in lu]
    if restricted:
        return l1, [u*f for f in lu]
    if n%p:
        p12 = (p+1)//2
        gam_1 = [  g for L in [expand1(f, range(1,p12)) for f in l1] for g in L]
        gam_u = [u*g for L in [expand1(f, range(1,p12)) for f in lu] for g in L]
        return gam_1, gam_u
    gam_1 = [  g for L in [expand2(f, range(1,p)) for f in l1] for g in L]
    gam_u = [u*g for L in [expand2(f, range(1,p)) for f in lu] for g in L]
    return gam_1, gam_u

def make_gammas_even_iter(n,p, code="1"):
    """Read from file "gamma{n}_{p}.out" and return an iterator through
    the set Gamma(n,1) (if code=="1") or Gamma(n,u) (if code=="u"), up
    to affine transforms.
    """
    assert n%2==0
    F = GF(p)
    Fx = PolynomialRing(F, 'x')
    u = a_nonsquare(F)
    lc = a_nonsquare(F) if code=="u" else F(1)
    coeff_iter = read_gamma_c_output_iter(n, p, u, "gamma{}_{}.out".format(n,p), code)
    n = 0
    for coeffs in coeff_iter:
        n += 1
        if (n%1000000==0):
            print("Read {} coefficient lists".format(n))
        yield lc*Fx(coeffs)

def make_gammas_odd(n,p, restricted=False):
    """Read from file "gamma{n}_{p}.out" and return the complete sets
    Gamma(n,1), Gamma(n,u) for n odd.

    Restricted means f = (1 or u)*(x^n+0*x^{n-1}+c*x^{n-2}+...) with:

    p=3 (mod 4): c=0 or in {1,u}, representing an affine orbit of size p or p(p-1)/2 respectively;

    p=1 (mod 4): c=0 or in {1,u,u^2,u^3}, representing an affine orbit of size p or p(p-1)/4 respectively.

    """
    assert n%2==1
    F = GF(p)
    Fx = PolynomialRing(F, 'x')
    u = a_nonsquare(F)
    l1, lu = read_gamma_c_output(n, p, u, "gamma{}_{}.out".format(n,p))
    l1 = [Fx(coeffs) for coeffs in l1]
    lu = [Fx(coeffs) for coeffs in lu]
    p12 = (p+1)//2
    squs = [(a*a)%p for a in range(1,p12)]
    gam_1 = []
    gam_u = []

    if n%p==0:
        for f in l1:
            flist = [f] if restricted else expand2(f, squs)
            glist = [u*scale(f1,u) for f1 in flist]
            gam_1 += flist
            if f[n-1]:
                gam_u += glist
        for f in lu:
            flist = [f] if restricted else expand2(f, squs)
            glist = [scale(f1,u) for f1 in flist]
            gam_u += [u*f1 for f1 in flist]
            if f[n-1]:
                gam_1 += glist
        return gam_1, gam_u

    if p%4==3:
        if restricted:
            return l1, [u*f for f in lu]
        gam_1 = [  g for L in [expand1(f, squs) for f in l1] for g in L]
        gam_u = [u*g for L in [expand1(f, squs) for f in lu] for g in L]
        return gam_1, gam_u

    # now p%4==1
    squs_mod = [a for a in squs if a < p12]
    for f in l1:
        flist = [f] if restricted else expand1(f, squs_mod)
        gam_1 += flist
        if f[n-2]:
            gam_u += [u*scale(f1,u) for f1 in flist]
    for f in lu:
        flist = [f] if restricted else expand1(f, squs_mod)
        gam_u += [u*f1 for f1 in flist]
        if f[n-2]:
            gam_1 += [scale(f1,u) for f1 in flist]
    return gam_1, gam_u

def make_gammas(n,p, restricted=False, store=False):
    print("(n,p)=({},{})".format(n,p))
    gam_1, gam_u = make_gammas_odd(n,p, restricted) if n%2 else make_gammas_even(n,p, restricted)
    if store:
        print("Storing Gamma({},1; {})".format(n,p))
        (Gamma_plus_short_dict if restricted else Gamma_plus_dict)[(p,n)] = gam_1
        if n%2==0:
            print("Storing Gamma({},u; {})".format(n,p))
            (Gamma_minus_short_dict if restricted else Gamma_minus_dict)[(p,n)] = gam_u
    return gam_1, gam_u

def make_gamma_counts(n,p, restricted=False, store=False):
    from basics import root_multiplicity_counts
    print("(n,p)=({},{})".format(n,p))
    gam_1, gam_u = make_gammas_odd(n,p, restricted) if n%2 else make_gammas_even(n,p, restricted)
    rmc_1 = root_multiplicity_counts(gam_1)
    rmc_u = root_multiplicity_counts(gam_u)
    if store:
        print("Storing multiplicity counts for Gamma({},1; {})".format(n,p))
        (Gamma_plus_short_mult_dict if restricted else Gamma_plus_mult_dict)[(p,n)] = rmc_1
        if n%2==0:
            print("Storing multiplicity counts for Gamma({},u; {})".format(n,p))
            (Gamma_minus_short_mult_dict if restricted else Gamma_minus_mult_dict)[(p,n)] = rmc_u
    return rmc_1, rmc_u

def make_gamma_counts_2(n):
    from basics import point_multiplicity_counts
    print("Storing multiplicity counts for Gamma({},1; 2)".format(n))
    Gamma_plus_short_mult_dict[(2,n)] = point_multiplicity_counts(Gamma_plus_dict[(2,n)])
    if n%2==0:
        print("Storing multiplicity counts for Gamma({},u; 2)".format(n))
        Gamma_minus_short_mult_dict[(2,n)] = point_multiplicity_counts(Gamma_minus_dict[(2,n)])

def make_gamma_counts_new(n,p, store=True):
    from basics import root_multiplicity_counts
    print("(n,p)=({},{})".format(n,p))
    if n%2:
        print("Not yet implemented for odd degree")
        return

    for code in ["1", "u"]:
        print("Reading C output with code {}".format(code))
        rmc = root_multiplicity_counts(make_gammas_even_iter(n,p, code))
        if store:
            print("Storing multiplicity counts for Gamma({},{}; {})".format(n,code,p))
            if code=="1":
                Gamma_plus_short_mult_dict[(p,n)] = rmc
            else:
                Gamma_minus_short_mult_dict[(p,n)] = rmc

def fill_restricted_gamma_dicts():
    global Gamma_plus_short_dict, Gamma_minus_short_dict
    for n in range(3,11):
        for p in primes(max_p_for_degree[n]+1):
            print("(n,p)=({},{})".format(n,p))
            gam_1, gam_u = make_gammas(n,p,True)
            Gamma_plus_short_dict[(p,n)] = gam_1
            if n%2==0:
                Gamma_minus_short_dict[(p,n)] = gam_u

############  Obsolete code for Delta sets ######################################

# Initialize dicts to store the Delta sets but do not reset on reload!
# try:
#     nd = len(Delta_dict)
# except NameError:
#     Delta_dict = {}

# def initialize_Delta_dicts():
#     global Delta_dict
#     Delta_dict = {}

# # Save to file and restore from file for Gammas and Deltas:
# def save_Deltas(filename="Delta"):
#     save(Delta_dict, filename)

# def restore_Deltas(filename="Delta"):
#     global Delta_dict
#     Delta_dict.update(load(filename))

# def Delta(d,F=None):
#     """Return a list of f of even degree d, homogeneous with no smooth
#     points but not of the form u*h^2.  Includes scalings (the
#     condition is invariant under scaling by squares).
#     """
#     if F==None or d%2==1 or d<6 :
#        return []
#     if F in ZZ:
#         q = F
#     else:
#         q = F.cardinality()
#     if (d==6 and q>11):
#         return []
#     if not (q,d) in Delta_dict:
#         if q==2:
#             Delta_dict[(q,d)] = Delta2(d)
#             return Delta_dict[(q,d)]
#         if F in ZZ:
#             F = GF(q)
#         print("Computing Delta({},{})".format(d,F))
#         u = a_nonsquare(F)
#         flist = homog(F,d) # up to scaling
#         # consider both f and u*f
#         D1 =  [f for f in flist if not is_square_homog(u*f) and no_smooth_points_homog(f)]
#         D2 =  [u*f for f in flist if not is_square_homog(f) and no_smooth_points_homog(u*f)]
#         # D1+D2 is the result up to scaling by squares.
#         sq = [F(a)**2 for a in range(1,((q-1)//2)+1)]
#         Delta_dict[(q,d)] = flatten([[a*f for f in D1+D2] for a in sq])
#     return Delta_dict[(q,d)]

# def Delta2(d):
#     """Return a list of (f,h) homogeneous of degrees (d,<=(d/2)) with d even,
#     such that z^2+h*z+f has no smooth points and either factors over
#     F_2 with distinct factors or is orrediucible over F_4.
#     """
#     F2 = GF(2)
#     Fxy = PolynomialRing(F2,['x','y'])
#     D = [(f,h) for f in homog(F2,d)+[Fxy(0)] for h in homog(F2,d//2)]
#     #print("{} (f,h) pairs in degree {}".format(len(D),d))
#     D = [fh for fh in D if no_smooth_points_mod2(*fh)]
#     #print("{} (f,h) pairs have no smooth points".format(len(D)))
#     D = [fh for fh in D if nfactors_mod2(*fh,abs=False)==[1,1] or nfactors_mod2(*fh,abs=True)==[1]]
#     #print("{} of those have are abs. irred.  or split over F2".format(len(D)))
#     return D

# def show_Delta(verbose=False):
#     for k in sorted(Delta_dict.keys()):
#         if verbose:
#             print("(p,d)={}: {}".format(k,Delta_dict[k]))
#         else:
#             print("(p,d)={}: {} elements".format(k,len(Delta_dict[k])))


