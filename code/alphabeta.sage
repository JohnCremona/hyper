from sage.all import (save, load, divisors, moebius, prod, factorial, flatten, polygen, infinity, xmrange_iter)
from sage.all import (QQ, ZZ, GF, FunctionField, PolynomialRing, ProjectiveSpace)

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

# Save to file and restore from file for Gammas and Deltas:
def save_Deltas(filename="Delta"):
    save(Delta_dict, filename)

def save_Gammas(filename="Gamma"):
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict], ["plus", "minus"]):
        f = "_".join([filename, suffix])
        print("Saving {}".format(f))
        save(Gdict, f)

# The restore functions use the update() method so that local values
# are preserved, but NB if the same key exists locally and on file
# then the file version will overwrite the local one.

def restore_Deltas(filename="Delta"):
    global Delta_dict
    Delta_dict.update(load(filename))

def restore_Gammas(filename="Gamma"):
    global Gamma_plus_dict, Gamma_minus_dict
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict], ["plus", "minus"]):
        f = "_".join([filename, suffix])
        print("Restoring {}".format(f))
        Gdict.update(load(f))

# Initialize dicts to store the alphas and betas but do not reset on reload!
# The alpha and beta values for subscripts 0,1,2 are known directly.
try:
    n = len(alpha_0_dict)
except NameError:
    print("Initializing alpha^0_i for i=0,1,2 to 0,1,1/2")
    alpha_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(alpha_plus_dict)
except NameError:
    print("Initializing alpha^+_i for i=0,1,2 to 1,1,1/p with p={}".format(pp))
    alpha_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1/pp}
try:
    n = len(alpha_minus_dict)
except NameError:
    print("Initializing alpha^-_i for i=0,1,2 to 0,1,1/(p+1) with p={}".format(pp))
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

def initialize_alpha_dicts():
    global alpha_0_dict, alpha_plus_dict, alpha_minus_dict
    print("Initializing alpha^0_i for i=0,1,2 to 0,1,1/2")
    alpha_0_dict =      {(0,pp):0, (1,pp):1, (2,pp):1/2}
    print("Initializing alpha^+_i for i=0,1,2 to 1,1,1/p with p={}".format(pp))
    alpha_plus_dict =   {(0,pp):1, (1,pp):1, (2,pp):1/pp}
    print("Initializing alpha^-_i for i=0,1,2 to 0,1,1/(p+1) with p={}".format(pp))
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

try:
    n = len(beta_0_dict)
except NameError:
    print("Initializing beta^0_i for i=0,1,2 to 0,1,1/2")
    beta_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(beta_plus_dict)
except NameError:
    print("Initializing beta^+_i for i=0,1,2 to 1,1,1")
    beta_plus_dict = {(0,pp):1, (1,pp):1, (2,pp):1}
try:
    n = len(beta_minus_dict)
except NameError:
    print("Initializing beta^-_i for i=0,1,2 to 0,1,p/(p+1) with p={}".format(pp))
    beta_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

def initialize_beta_dicts():
    global beta_0_dict, beta_plus_dict, beta_minus_dict
    print("Initializing beta^0_i for i=0,1,2 to 0,1,1/2")
    beta_0_dict =     {(0,pp):0, (1,pp):1, (2,pp):1/2}
    print("Initializing beta^+_i for i=0,1,2 to 1,1,1")
    beta_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1}
    print("Initializing beta^-_i for i=0,1,2 to 0,1,p/(p+1) with p={}".format(pp))
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
                       range(m1(phi,j))])/prod([factorial(m2(phi,[j,i]))
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
        if q==2:
            res = [(f,h) for f in monics(F,d,d%2)
                         for h in monics(F,(d+1)//2,(d+1)%2)
                   if no_smooth_points_mod2(f,h)]
        else:
            res = Gamma_new(d,F,+1)
        Gamma_plus_dict[(q,d)] = res
    #print("accessing Gamma^+ with p={}, degree {}".format(q,d))
    return Gamma_plus_dict[(q,d)]

def Gamma_default(d,F,plusorminus):
    if plusorminus==+1:
       return Gamma_plus_default(d,F)
    else:
       return Gamma_minus_default(d,F)

def Gamma_plus_default(d,F):
    p = F.cardinality()
    m = monics if d%p==0 else monics0
    res = [f for f in m(F,d) if no_smooth_points(f)]
    if d%p==0:
       return res
    x = res[0].parent().gen()
    return [f(x+b) for b in F for f in res]

def Gamma_minus_default(d,F):
    p = F.cardinality()
    u = a_nonsquare(F)
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
    t = ff0[d-4]-s^2
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
        temp = [(u1*x^2-s*u1*x+k-t)*ff0 + sum([w[j]*ff[j] for j in range(d-2)])
           for w in xmrange_iter([ns for _ in range(d-2)])]
        assert all([list(f)[-3:] == [k,0,u1] for f in temp])
        temp = [f for f in temp if test(f)]
        if k:
           temp = [f(r*x)/r^d for r in rr for f in temp]
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
    u, with no smooth points but not of the form u*h^2.
    """
    if F==None:
       return []
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if not (q,d) in Gamma_minus_dict:
        if d%2:
            Gamma_minus_dict[(q,d)] = Gamma_plus(d,F)
            return Gamma_minus_dict[(q,d)]
        if F in ZZ:
            F = GF(q)
        print("Computing Gamma_minus({},{})".format(d,F))
        if q==2:
            res = [(f,h) for f in monics(F,d,1)
                         for h in monics(F,d//2,1)
             if no_smooth_points_mod2(f,h) and is_irred_mod2(f,h,True)]
        else:
            res = Gamma_new(d,F,-1)
        Gamma_minus_dict[(q,d)] = res
    #print("accessing Gamma^- with p={}, degree {}".format(q,d))
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
    """ Function to check entries in Table in paper
    """
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

    res = [len(ff) for ff in [Gamma_plus(1,F),
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
    if p in table:
       if res==table[p]:
          print("p={} OK".format(p))
       else:
          print("p={} not OK, table is\n{} but we get\n{}".format(p,table[p],res))
    return res

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
    if F==None or d%2==1 or d<6 :
       return []
    if F in ZZ:
        q = F
    else:
        q = F.cardinality()
    if (d==6 and q>11):
        return []
    if not (q,d) in Delta_dict:
        if q==2:
            Delta_dict[(q,d)] = Delta2(d)
            return Delta_dict[(q,d)]
        if F in ZZ:
            F = GF(q)
        print("Computing Delta({},{})".format(d,F))
        u = a_nonsquare(F)
        flist = homog(F,d) # up to scaling
        # consider both f and u*f
        D1 =  [f for f in flist if not is_square_homog(u*f) and no_smooth_points_homog(f)]
        D2 =  [u*f for f in flist if not is_square_homog(f) and no_smooth_points_homog(u*f)]
        # D1+D2 is the result up to scaling by squares.
        sq = [F(a)^2 for a in range(1,((q-1)//2)+1)]
        Delta_dict[(q,d)] = flatten([[a*f for f in D1+D2] for a in sq])
    return Delta_dict[(q,d)]

def Delta2(d):
    """Return a list of (f,h) homogeneous of degrees (d,<=(d/2)) with d even,
    such that z^2+h*z+f has no smooth points and either factors over
    F_2 with distinct factors or is orrediucible over F_4.
    """
    F2 = GF(2)
    Fxy = PolynomialRing(F2,['x','y'])
    D = [(f,h) for f in homog(F2,d)+[Fxy(0)] for h in homog(F2,d//2)]
    #print("{} (f,h) pairs in degree {}".format(len(D),d))
    D = [fh for fh in D if no_smooth_points_mod2(*fh)]
    #print("{} (f,h) pairs have no smooth points".format(len(D)))
    D = [fh for fh in D if nfactors_mod2(*fh,abs=False)==[1,1] or nfactors_mod2(*fh,abs=True)==[1]]
    #print("{} of those have are abs. irred.  or split over F2".format(len(D)))
    return D

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

def fh_term(f,h):
    """Helper function for beta^+, beta^-, mu_0 in case p=2.  In the paper
    this is expressed differently, as a double product over j up to
    the degree and eps, with multiplicities.  Here we just take the
    product over all roots.

    Note that if there is a root of multiplicity 1 then alpha^eps(1)=1
    and the result is 0, but this will only be called with f which
    have no such roots.

    This works equally well in the projective case.

    """
    return prod([(1-alpha_eps(eps)(j,2)) for P,(j,eps) in point_multiplicities(f,h)])

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

def beta_plus(i,p=pp,v=None, verbose=False):
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
            if verbose: print("setting beta_plus({},{})".format(i,p))
            b = beta_plus_dict[(i,p)] = 1
            return b
        pass
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
    # use Prop 3.3 (i)
    if verbose: print("Computing beta_plus({},{})".format(i,p))
    Fp = GF(p) if p in ZZ else None
    G = Gamma_plus(i,Fp)
    if p==2:
        e = (3*i+1)//2 if i%2 else 3*i//2
        b = 1 - sum([fh_term(f,h) for f,h in G])/p^e
    else:
        b = 1 - sum([f_term(f,p) for f in G])/p^i

    try:
        b=F(b)
        if verbose: print("setting beta_plus({},{})".format(i,p))
        beta_plus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            if verbose:
                print("setting beta_plus({},{})".format(i,p))
                print("{}={}".format(v0,b))
            beta_plus_dict[(i,p)] = b
    return b

def beta_minus(i,p=pp,v=None, verbose=False):
    """beta^-_i(p).

    Computed values are stored in beta_minus_dict keyed on (i,p).
    """
    try:
        return beta_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_minus({},{})".format(i,p))
            b = beta_minus_dict[(i,p)] = [0,1,p/(p+1)][i]
            return b
    if i%2==1:
        if verbose: print("setting beta_minus({},{})".format(i,p))
        b = beta_minus_dict[(i,p)] = beta_plus(i,p,v)
        return b
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
    # now i is even, use Prop 3.3(ii)
    if verbose: print("Computing beta_minus({},{})".format(i,p))
    i2 = i//2
    Fp = GF(p) if p in ZZ else None
    G = Gamma_minus(i,Fp)
    if p==2:
        b = ( 1
              - sum([phi_term(phi,"affine",True,p,v) for phi in Phi(i2)]) / p^i2
              - sum([fh_term(f,h) for f,h in G]) / p^((3*i)//2))
    else:
        b = ( 1
              - sum([phi_term(phi,"affine",True,p,v) for phi in Phi(i2)]) / p^i2
              - sum([f_term(f,p) for f in G]) / p^i)
    try:
        b=F(b)
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

def beta_0(i,p=pp,v=None, verbose=False):
    """beta^0_i(p).

    Computed values are stored in beta_0_dict keyed on (i,p).
    """
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting beta_0({},{})".format(i,p))
            b =  beta_0_dict[(i,p)] = [0,1,1/2][i]
            return b
    make_betas(i-1,p)
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
    if verbose: print("Computing beta_0({},{})".format(i,p))
    b = 1 - sum([phi_term(phi,"affine",False,p,v) for phi in Phi(i)])
    try:
        b=F(b)
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

def alpha_0(i,p=pp,v=None, verbose=False):
    """ alpha^0_i(p).

    Computed values are stored in alpha_0_dict keyed on (i,p).
    """
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_0({},{})".format(i,p))
            a = alpha_0_dict[(i,p)] = [0,1,1/2][i]
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
    make_alphas(i-1,p)
    if verbose: print("Computing alpha_0({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [beta(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [beta_0(k,p,v) for k in range(j,-1,-1)]
    if i%2==0:
       blist += [beta_0(i,p,v)]
    else:
       blist += [beta(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        if verbose: print("setting alpha_0({},{})".format(i,p))
        alpha_0_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting alpha_0({},{})".format(i,p))
            alpha_0_dict[(i,p)] = a
    return a

def alpha_plus(i,p=pp,v=None, verbose=False):
    """ alpha^+_i(p).

    Computed values are stored in alpha_plus_dict keyed on (i,p).
    """
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_plus({},{})".format(i,p))
            a = alpha_plus_dict[(i,p)] = [1,1,1/p][i]
            return a
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
    if verbose: print("Computing alpha_plus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [beta_0(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [beta(k,p,v) for k in range(j,-1,-1)]
    if i%2==0:
       blist += [beta_plus(i,p,v)]
    else:
       blist += [beta_0(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        if verbose: print("setting alpha_plus({},{})".format(i,p))
        alpha_plus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        if verbose: print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            if verbose:
                print("{}={}".format(v0,a))
                print("setting alpha_plus({},{})".format(i,p))
            alpha_plus_dict[(i,p)] = a
    return a

def alpha_minus(i,p=pp,v=None, verbose=False):
    """ alpha^-_i(p).

    Computed values are stored in alpha_minus_dict keyed on (i,p).
    """
    try:
        return alpha_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            if verbose: print("setting alpha_minus({},{})".format(i,p))
            a = alpha_minus_dict[(i,p)] = [0,1,1/(p+1)][i]
            return a
    if i%2==1:
        if verbose: print("setting alpha_minus({},{})".format(i,p))
        alpha_minus_dict[(i,p)] = alpha_plus(i,p)
        return alpha_minus_dict[(i,p)]
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
    if verbose: print("Computing alpha_minus({},{})".format(i,p))
    i2 = i-2
    blist = []
    for j in range(i2+1):
      if j%2==0:
         blist += [beta_0(k,p,v) for k in range(j,-1,-1)]
      else:
         blist += [beta(k,p,v) for k in range(j,-1,-1)]
    blist += [beta_minus(i,p,v)]
    if verbose: print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
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

def make_alphas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 alphas with subscript i
    after first computing all alphas and betas with smaller
    subscripts.
    """
    if verbose:
        print("Making all alpha_{} for p={}".format(i,p))
    for j in range(3,i):
        make_alphas(j,p)
        make_betas(j,p)
    a = alpha_plus(i,p)
    if verbose:
        print("alpha_plus({},{}) = {}".format(i,p,a))
    a = alpha_minus(i,p)
    if verbose:
        print("alpha_minus({},{}) = {}".format(i,p,a))
    a = alpha_0(i,p)
    if verbose:
        print("alpha_0({},{}) = {}".format(i,p,a))

def make_betas(i, p=pp, verbose=False):
    """Compute (and optionally display) all 3 betas with subscript i
    after first computing all alphas and betas with smaller
    subscripts.
    """
    for j in range(3,i):
        make_alphas(j,p)
        make_betas(j,p)
    b = beta_plus(i,p)
    if verbose:
        print("beta_plus({},{}) = {}".format(i,p,b))
    b = beta_minus(i,p)
    if verbose:
        print("beta_minus({},{}) = {}".format(i,p,b))
    b = beta_0(i,p)
    if verbose:
        print("beta_0({},{}) = {}".format(i,p,b))

def check_value(ab,i,eps,val,p=pp):
    myval = [alpha_minus,alpha_0,alpha_plus][eps+1](i,p) if ab=="alpha" else [beta_minus,beta_0,beta_plus][eps+1](i,p)
    sup = ["-","0","+"][eps+1]
    if myval==val:
        print("{}_{}^{}({}) OK".format(ab,i,sup,p))
    else:
        print("WRONG {}_{}^{}({}) = {}, should be {}".format(ab,i,sup,p,myval,val))

def check3():
    """ Check that all 3 alpha_3^eps are correct for p=3 and p generic.
    """
    make_alphas(3,3)
    check_value("alpha",3,+1, 50246/177147, 3)
    check_value("alpha",3,-1, 50246/177147, 3)
    check_value("alpha",3 ,0, 431/729,3)

    make_alphas(3)
    check_value("alpha",3,+1, (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8))
    check_value("alpha",3,-1, (6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8))
    check_value("alpha",3, 0, (pp**3+pp**2-2*pp+2)/(2*pp**3))

    make_alphas(3,2)
    check_value("alpha",3,+1, 807/2048, 2)
    check_value("alpha",3,-1, 807/2048, 2)
    check_value("alpha",3 ,0, 39/64,2)


def check4():
    """ Check that all 3 alpha_4^eps are correct for p=3, p=5 and p generic.
    """
    make_alphas(4,3)
    make_alphas(4,5)
    make_alphas(4)
    check_value("alpha",4,+1, 16600/59049, 3)
    check_value("alpha",4,+1, 352624/1953125, 5)
    check_value("alpha",4,+1, (pp**2+1)*(2*pp**3-pp**2-2*pp+2)/(2*pp**6))

    check_value("alpha",4,-1, (2*pp**10+3*pp**9-pp**5+2*pp**4-2*pp**2-3*pp-1)/(2*(pp+1)**2 *(pp**9-1)))
    check_value("alpha",4, 0, (4*pp**10+8*pp**9-4*pp**8+4*pp**6-3*pp**4+pp**3-5*pp-5)/(8*(pp+1)*(pp**9-1)))

    make_alphas(4,2)
    check_value("alpha",4,+1, 407079/1048576, 2)
    check_value("alpha",4,-1, 3569/9198, 2)
    check_value("alpha",4 ,0, 7369/12264,2)


def check5():
    """ Check that all alpha_5^eps and beta_5^eps are correct for p=3.
    """
    make_alphas(5,3)
    check_value("alpha",5, 0, 1493687989147/2541865828329, 3)
    check_value("alpha",5,+1, 13670659773280445407/48630661836227715204, 3)
    check_value("alpha",5,-1, 13670659773280445407/48630661836227715204, 3)
    check_value("alpha",5,+1,(p^26 + 1/2*p^25 - 1/2*p^24 + 1/2*p^23 - 1/2*p^22 + p^20 - 1/2*p^19 - 11/30*p^17 + 2/15*p^16 - 1/12*p^15 + 1/6*p^14 - 3/10*p^13 + 1/5*p^12 + 1/4*p^11 - 1/3*p^7 + 1/6*p^5 - 5/6*p^3 + 3/2*p^2 + p - 1)/(p^27 + p^26))
    check_value("alpha",5,-1,(p^26 + 1/2*p^25 - 1/2*p^24 + 1/2*p^23 - 1/2*p^22 + p^20 - 1/2*p^19 - 11/30*p^17 + 2/15*p^16 - 1/12*p^15 + 1/6*p^14 - 3/10*p^13 + 1/5*p^12 + 1/4*p^11 - 1/3*p^7 + 1/6*p^5 - 5/6*p^3 + 3/2*p^2 + p - 1)/(p^27 + p^26))
    check_value("alpha",5,0,(1/2*p^13 + p^12 - 1/2*p^11 + 1/2*p^9 - 1/3*p^7 + 1/6*p^5 - 5/6*p^3 + 3/2*p^2 + p - 1)/(p^13 + p^12))

    make_betas(5,3)
    check_value("beta",5, 0, 129514464056263/205891132094649, 3)
    check_value("beta",5,+1, 160260073/172186884, 3)
    check_value("beta",5,-1, 160260073/172186884, 3)
    check_value("beta",5,+1,1)
    check_value("beta",5,-1,1)
    check_value("beta",5,0,  (19/30*p^17 + 19/30*p^16 - 1/12*p^15 + 1/6*p^14 - 3/10*p^13 + 1/5*p^12 + 1/4*p^11 - 1/3*p^7 + 1/6*p^5 - 5/6*p^3 + 3/2*p^2 + p - 1)/(p^17 + p^16))

def check6():
    """ Check that all alpha_6^eps and beta_6^eps are correct for p=3.
    """
    make_alphas(6,3)
    check_value("alpha",6, 0, 26377476341107224253/44887561041873369600, 3)
    check_value("alpha",6,+1, 605398279518845051650813/2153584544086426253951538, 3)
    check_value("alpha",6,-1, 27339928051320364957/97256382257392300800, 3)
    check_value("alpha",6,+1,(p^24 + 1/2*p^23 + 1/2*p^22 + p^21 + p^19 + p^18 + 1/2*p^17 + p^16 - 7/8*p^15 + 2/3*p^14 - 1/2*p^13 + 5/24*p^12 + 1/2*p^11 - 3/2*p^10 + 3/2*p^9 + 1/2*p^8 + 1/2*p^6 + 1/3*p^5 + 1/2*p^4 + 1/6*p^3 + 1/2*p^2 + p - 1)/(p^25 + p^24 + p^23 + p^22 + p^21 + p^20 + p^19 + p^18 + p^17))
    check_value("alpha",6,-1,(p^28 + 7/2*p^27 + 6*p^26 + 17/2*p^25 + 11*p^24 + 13*p^23 + 16*p^22 + 39/2*p^21 + 45/2*p^20 + 193/8*p^19 + 577/24*p^18 + 24*p^17 + 191/8*p^16 + 583/24*p^15 + 24*p^14 + 23*p^13 + 25*p^12 + 53/2*p^11 + 51/2*p^10 + 73/3*p^9 + 71/3*p^8 + 121/6*p^7 + 37/2*p^6 + 47/3*p^5 + 41/3*p^4 + 55/6*p^3 + 14/3*p^2 + 13/6*p + 2/3)/(p^29 + 4*p^28 + 8*p^27 + 12*p^26 + 16*p^25 + 20*p^24 + 24*p^23 + 28*p^22 + 32*p^21 + 35*p^20 + 36*p^19 + 36*p^18 + 36*p^17 + 36*p^16 + 36*p^15 + 36*p^14 + 36*p^13 + 36*p^12 + 36*p^11 + 36*p^10 + 35*p^9 + 32*p^8 + 28*p^7 + 24*p^6 + 20*p^5 + 16*p^4 + 12*p^3 + 8*p^2 + 4*p + 1))
    check_value("alpha",6,0,(1/2*p^35 + 5/2*p^34 + 5*p^33 + 7*p^32 + 19/2*p^31 + 25/2*p^30 + 91/6*p^29 + 35/2*p^28 + 20*p^27 + 133/6*p^26 + 22*p^25 + 22*p^24 + 49/2*p^23 + 26*p^22 + 103/4*p^21 + 3775/144*p^20 + 473/18*p^19 + 105/4*p^18 + 3751/144*p^17 + 1907/72*p^16 + 79/3*p^15 + 177/8*p^14 + 439/24*p^13 + 33/2*p^12 + 1003/72*p^11 + 211/18*p^10 + 147/16*p^9 + 56/9*p^8 + 271/72*p^7 + 95/48*p^6 + 11/8*p^5 + 17/24*p^4 - 1/2*p - 1/2)/(p^35 + 4*p^34 + 8*p^33 + 12*p^32 + 16*p^31 + 20*p^30 + 24*p^29 + 28*p^28 + 32*p^27 + 35*p^26 + 36*p^25 + 36*p^24 + 36*p^23 + 36*p^22 + 36*p^21 + 36*p^20 + 36*p^19 + 36*p^18 + 36*p^17 + 36*p^16 + 35*p^15 + 32*p^14 + 28*p^13 + 24*p^12 + 20*p^11 + 16*p^10 + 12*p^9 + 8*p^8 + 4*p^7 + p^6))

    make_betas(6,3)
    check_value("beta",6, 0, 690037935950003/1098030248972800, 3)
    check_value("beta",6,+1, 28366779023771/30502389939948, 3)
    check_value("beta",6,-1, 9541669997405587/10262359634630400, 3)
    check_value("beta",6,+1,1)
    check_value("beta",6,-1,(p^31 + 4*p^30 + 8*p^29 + 11*p^28 + 13*p^27 + 29/2*p^26 + 103/6*p^25 + 56/3*p^24 + 133/6*p^23 + 68/3*p^22 + 68/3*p^21 + 127/6*p^20 + 62/3*p^19 + 65/3*p^18 + 139/6*p^17 + 193/8*p^16 + 577/24*p^15 + 24*p^14 + 191/8*p^13 + 583/24*p^12 + 23*p^11 + 19*p^10 + 17*p^9 + 31/2*p^8 + 25/2*p^7 + 59/6*p^6 + 15/2*p^5 + 5*p^4 + 7/3*p^3 + 3/2*p^2 + 2*p + 1)/(p^31 + 4*p^30 + 8*p^29 + 12*p^28 + 16*p^27 + 20*p^26 + 24*p^25 + 28*p^24 + 32*p^23 + 35*p^22 + 36*p^21 + 36*p^20 + 36*p^19 + 36*p^18 + 36*p^17 + 36*p^16 + 36*p^15 + 36*p^14 + 36*p^13 + 36*p^12 + 35*p^11 + 32*p^10 + 28*p^9 + 24*p^8 + 20*p^7 + 16*p^6 + 12*p^5 + 8*p^4 + 4*p^3 + p^2))
    check_value("beta",6,0,(91/144*p^29 + 91/36*p^28 + 5*p^27 + 1075/144*p^26 + 719/72*p^25 + 37/3*p^24 + 117/8*p^23 + 427/24*p^22 + 21*p^21 + 1651/72*p^20 + 218/9*p^19 + 1169/48*p^18 + 427/18*p^17 + 1711/72*p^16 + 1159/48*p^15 + 187/8*p^14 + 545/24*p^13 + 49/2*p^12 + 26*p^11 + 101/4*p^10 + 301/12*p^9 + 95/4*p^8 + 85/4*p^7 + 223/12*p^6 + 33/2*p^5 + 29/2*p^4 + 10*p^3 + 11/2*p^2 + 5/2*p + 1/2)/(p^29 + 4*p^28 + 8*p^27 + 12*p^26 + 16*p^25 + 20*p^24 + 24*p^23 + 28*p^22 + 32*p^21 + 35*p^20 + 36*p^19 + 36*p^18 + 36*p^17 + 36*p^16 + 36*p^15 + 36*p^14 + 36*p^13 + 36*p^12 + 36*p^11 + 36*p^10 + 35*p^9 + 32*p^8 + 28*p^7 + 24*p^6 + 20*p^5 + 16*p^4 + 12*p^3 + 8*p^2 + 4*p + 1))

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
    make_alphas(2*g+2,p)
    make_betas(2*g+2, p)
    A = mu0_term_1(g,p)
    B = mu0_term_2(g,p)
    C = mu1_term(g,p)
    e = 3*g+5 if p==2 else 2*g+3
    ans0 =  ((p^(g+2)-1)/(2*p^(2*g+3)) * A + B/p^e + (p^(2*g+3)-1)/(p^(4*g+6)) * C) / (1-1/p^(4*g+6))
    ans1 =  ((p^(2*g+3)-1) * C + ans0) / p^(2*g+3)
    assert ans0 == (p^(g+2)-1)/(2*p^(2*g+3)) * A +  B/p^e + ans1/p^(2*g+3)
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
            return ie(alpha(n-i,p), beta(i,p))
        else:
            return (ie(alpha_plus(n-i,p), beta_plus(i,p))+ie(alpha_minus(n-i,p), beta_minus(i,p)))/2

    return (p-1)*sum([term(i)*p**i for i in range(n+1)])/p**(n+1)

def rho_1(n,p=pp):
    """Return rho_1(n) for p an odd prime or generic, n even.  This is the
    *relative* local density of soluble y^2=f(x), restricted to f with
    valuation 1.

    This different from the formula give in Prop 3.23 of hyper.pdf,
    which only involves the alpha's.
    """
    def term(i):
        """ prob. soluble if deg(f/p mod p)=i
        """
        return ie(alpha_0(n-i,p), beta_0(i,p))
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
#             return ie(alpha(d-i,p), beta(i,p))
#         else:
#             return (ie(alpha_plus(d-i,p), beta_plus(i,p))+ie(alpha_minus(d-i,p), beta_minus(i,p)))/2
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
#         return ie(alpha_0(d-i,p), beta_0(i,p))
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

