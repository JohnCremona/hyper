# Initialize dicts to store the Gamma_plus/minus and Delta sets but do
#  not reset on reload.  The dicts will be initialized if they don't
#  exist (e.g. on first loading the file) or have no entries.
#  Re-initialization of the dicts is done by the initialize_dicts()
#  functions.

from sage.all import ZZ, GF, PolynomialRing, polygen, prod, save, load, flatten, xmrange_iter, ProjectiveSpace
from basics import monics, monics0, homog

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
    #print("accessing Gamma(d,1) with p={}".format(d,q))
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
    #print("accessing Gamma(d,u) with p={}".format(d,q))
    return Gamma_minus_dict[(q,d)]

def show_Gamma(verbose=False):
    for d,dname in zip([Gamma_plus_dict, Gamma_minus_dict], ["Gamma(n,1)","Gamma(n,u)"]):
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
        sq = [F(a)**2 for a in range(1,((q-1)//2)+1)]
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

