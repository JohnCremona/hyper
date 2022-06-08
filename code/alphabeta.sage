from sage.all import (save, load, prod, polygen, xmrange_iter, moebius, primes, Infinity, sign, binomial)
from sage.all import (QQ, ZZ, GF, PolynomialRing, ProjectiveSpace)

from basics import (Qp, pp, affine, subs)

max_p_for_degree = {1:0, 2:0, 3:3, 4:5, 5:11, 6:13, 7:19, 8:23, 9:37, 10:37}

################################# Set up dicts for Gamma sets  ##################################

# The Gamma_plus, Gamma_minus dicts with keys (p,d) have values
# Counter objects, counting sorted lists of pairs (m,sign).

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

def save_Gammas():
    filename="Gamma"
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict],
                             ["plus", "minus"]):
        f = "_".join([filename, suffix])
        print("Saving {}".format(f))
        save(Gdict, f)

def restore_Gammas(filename="Gamma"):
    global Gamma_plus_dict, Gamma_minus_dict
    for Gdict, suffix in zip([Gamma_plus_dict, Gamma_minus_dict],
                             ["plus", "minus"]):
        f = "_".join([filename, suffix])
        print("Restoring {}".format(f))
        Gdict.update(load(f))

################################# Set up dicts for alphas and betas  ##################################

# Initialize dicts to store the betas and alphas but do not reset on reload!
# The beta and alpha values for subscripts 0,1,2 are known directly.

# alpha_dict has keys (n,eps,p) where n>=0, eps is in {"1", "u", "p"} and p is pp or a prime.

def initialize_alpha_dict():
    global alpha_dict
    print("Initializing alpha(i,eps,p) for i=0,1,2")
    alpha_dict = {(0,"p",pp):0, (1,"p",pp):1, (2,"p",pp):1/2,
                  (0,"1",pp):1, (1,"1",pp):1, (2,"1",pp):1,
                  (0,"u",pp):0, (1,"u",pp):1, (2,"u",pp):pp/(pp+1)}

def initialize_beta_dict():
    global beta_dict
    print("Initializing beta(i,eps,p) for i=0,1,2")
    beta_dict = {(0,"p",pp):0, (1,"p",pp):1, (2,"p",pp):1/2,
                 (0,"1",pp):1, (1,"1",pp):1, (2,"1",pp):1/pp,
                 (0,"u",pp):0, (1,"u",pp):1, (2,"u",pp):1/(pp+1)}

def initialize_alpha_beta_dicts():
    initialize_alpha_dict()
    initialize_beta_dict()

try:
    n = len(alpha_dict)
except NameError:
    initialize_alpha_dict()

try:
    n = len(beta_dict)
except NameError:
    initialize_beta_dict()

################################# Set up dict for N_sigma  ##################################

def initialize_N_dict():
    global N_dict
    N_dict = {}

try:
    n = len(N_dict)
except NameError:
    N_dict = {}

def initialize_all_dicts():
    initialize_alpha_beta_dicts()
    initialize_Gamma_dicts()
    initialize_N_dict()

################################# Functions to display dicts  ##################################

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t(i,eps,p)={}: {}".format(k,d[k]))

def show_beta_dicts():
    show1dict(beta_dict, "beta(n,eps,p)")

def show_alpha_dicts():
    show1dict(alpha_dict, "alpha(n,eps,p)")

def show_dicts():
    show_alpha_dicts()
    show_beta_dicts()

################################# Functions for factorization patterns etc  #######################

def N_monics(j, p=pp):
    """The number of degree j monic irreducibles in GF(p)[X].
    """
    global N_dict
    if not (j,p) in N_dict:
        N_dict[(j,p)] = sum([moebius(d)*p**(j//d) for d in ZZ(j).divisors()]) / j
    return N_dict[(j,p)]

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


def N_phi(phi, p=pp):
    """For phi a factorization pattern, returns the number of monic
    polynomials over F_p with factorizatino pattern phi: equation (6)
    in the paper.
    """
    d = deg_fp(phi)
    return prod([prod([N_monics(j,p)-i for i in range(m1(phi,j))]) /
                 prod([ZZ(m2(phi,[j,i])).factorial() for i in range(1,d+1)])
                 for j in range(1,d+1)])

def lambda_A(phi, p=pp):
    """ The probability that a monic polynomial of degree deg(phi) has factorization pattern phi.
    """
    return N_phi(phi, p) / deg_fp(phi)


##########################################################################################
#

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


##########################################################################################
#
# code for computing Gamma_plus(n) and Gamma_minus(n) for p=2
#
def Gamma_plus_2(d):
    from basics import monics
    F = GF(2)
    res = [[f,h] for f in monics(F,d,d%2)
           for h in monics(F,(d+1)//2,(d+1)%2)
           if no_smooth_points_mod2(f,h)]
    return res

def Gamma_minus_2(d):
    from basics import monics
    F = GF(2)
    res = [[f,h] for f in monics(F,d,1)
           for h in monics(F,d//2,1)
           if no_smooth_points_mod2(f,h) and is_irred_mod2(f,h,True)]
    return res

##########################################################################################
#
# Look up Gamma multiplicities from dicts
#
def Gamma_plus_mults(d,p):
    """Counter giving frequencies of each pattern of signed root
    multiplicities for f in Gamma(d,1; p)
    """
    if (p,d) in Gamma_plus_dict:
        return Gamma_plus_dict[(p,d)]
    raise RuntimeError("No stored Gamma_plus multiplicities for degree {}, p={}".format(d,p))

def Gamma_minus_mults(d,p):
    """Counter giving frequencies of each pattern of signed root
    multiplicities for f in Gamma(d,u; p)
    """
    if (p,d) in Gamma_minus_dict:
        return Gamma_minus_dict[(p,d)]
    raise RuntimeError("No stored Gamma_minus multiplicities for degree {}, p={}".format(d,p))

##########################################################################################
#
# Display Gamma multiplicities from dicts
#
def show_Gamma(verbose=False):
    for d,dname in zip([Gamma_plus_dict, Gamma_minus_dict], ["Gamma(n,1) multiplicities", "Gamma(n,u) multiplicities"]):
        print("\n{} entries".format(dname))
        for k in sorted(d.keys()):
            if verbose:
                print("\t(p,d)={}: {}".format(k,d[k]))
            else:
                print("\t(p,d)={}: {} elements".format(k,len(d[k])))

def convert_key(k):
    mults = sorted([s*m for m,s in k])
    return "[" + ",".join("{:+d}".format(m) for m in mults) + "]"

def show_Gamma_mults(n, p, outfile=None):
    """
    Display Gamma(n; p) nicely in a format easily comparable
    with C output.  Either shown on screen or sent to a filename if
    given as 3rd arguement.
    """
    if outfile:
        with open(outfile, 'w') as output:
            for d,t in zip([Gamma_plus_dict, Gamma_minus_dict],  ["1", "u"]):
                if t=="u" and n%2:
                    continue
                dname = "Gamma({},{})".format(n,t)
                try:
                    counts = d[(p,n)]
                except KeyError:
                    continue
                output.write("{}: {} different patterns\n".format(dname, len(counts)))
                for k in sorted(counts.keys(), key=lambda x:tuple(xi[0]*xi[1] for xi in x)):
                    output.write("{} {} {}\n".format(t, convert_key(k), counts[k]))
    else:
        for d,t in zip([Gamma_plus_dict, Gamma_minus_dict],  ["1", "u"]):
            if t=="u" and n%2:
                continue
            dname = "Gamma({},{})".format(n,t)
            try:
                counts = d[(p,n)]
            except KeyError:
                continue
            print("{}: {} different patterns".format(dname, len(counts)))
            for k in sorted(counts.keys(), key=lambda x:tuple(xi[0]*xi[1] for xi in x)):
                print("{} {} {}".format(t, convert_key(k), counts[k]))

##########################################################################################
#
# Read Gamma multiplicities from C output, for storing in dicts
#
def read_Gamma_mults(n, p, filename=None, new_style=False):
    """Read C output file for degree n, prime p, and return two counters
    for Gamma_plus and Gamma_minus.  The C output file will not have
    any "u" lines when n is odd, so then the second counter is empty.

    When the newstyle flag is False (default), for "u" lines the
    multiplicity lists are for polynomials with leading coefficient u
    (quadratic non-residue), as is JC's C programs.  Otherwise they
    are for monic polynomials, as in the new definition and TF's
    output, and we switch signs for comparison.

    Currently the later code assumes that Gamma_minus multiplicities
    are old-style.

    """
    from collections import Counter
    if not filename:
        filename = "m{}gamma{}_{}.out".format("" if n%p else "x", n, p)
    print("Reading Gamma multiplicites for degree {}, p={}, from {}".format(n,p,filename))
    c1 = Counter()
    cu = Counter()
    with open(filename) as infile:
        for L in infile:
            if L[0] not in ["1", "u"]:
               continue
            t, code, mult = L.split()
            assert t in ["1", "u"]
            code = [] if code=="[]" else [int(m) for m in code[1:-1].split(",")]
            if t=="u" and new_style:
                code = [m if m%2 else -m for m in code]
            code = tuple(sorted((abs(m),sign(m)) for m in code))
            (c1 if t=="1" else cu)[code] = ZZ(mult)
    return c1, cu

##########################################################################################
#
# Check Gamma multiplicities agree with paper (old version, obsolete)
#
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

##########################################################################################
#
# Check Gamma multiplicities agree with paper (new version)
#
def one_row_from_mults(p):
    """ Function to check entries in Table in paper
    """
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
    if p not in table:
        print("No table row for p = {}".format(p))
        return
    d_list = [1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8]
    G_list = [Gamma_plus_dict if i in [0,1,2,4,5,7,8,10] else Gamma_minus_dict for i in range(11)]
    res = [sum(G[p,d].values()) for d,G in zip(d_list, G_list)]
    if res==table[p]:
        print("p={} OK".format(p))
    else:
        print("p={} not OK, table is\n{} but we get\n{}".format(p,table[p],res))
    return res

##########################################################################################
#

def T(r, eps, p=pp):
    """
    Helper function for R(r,eps,p)
    """
    #print("In T(r, eps, p) with r={}, eps={}, p={}".format(r,eps,p))
    if (r%2==1 if eps in ["1", "u"] else r%2==0):
        return 2*sum(p**s * alpha(s, "p", p) for s in range(r))
    else:
        return sum(p**s * (alpha(s, "1", p) + alpha(s, "u", p)) for s in range(r))

def R(n, eps, p=pp):
    """
    R(n,eps,p) = beta(n,eps,p) - p**-binomial(n,2) * alpha(n,eps,p)
    """
    #print("In R(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    return (p-1) * sum(p**(-binomial(r+1,2)) * T(r, eps, p) for r in range(1,n)) / 2

def sum_f_terms(n, eps, p=pp):
    """
    First helper function for S(), for eps=1,u.

    The reason for flipping + and - multiplicities when eps="u" is that
    we stored multiplicities for old-style Gamma(n,u;p) containing
    polys with leading coefficient u.
    """
    #print("In sum_f_terms(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    if p==pp or p>max_p_for_degree.get(n,Infinity):
        return 0
    eps1 = eps_decode[eps] # convert to +1,-1
    mults = Gamma_plus_mults(n,p) if eps1 == 1 else Gamma_minus_mults(n,p)
    # To flip signs we negate s in (j,s) when eps1=-1 and j is even
    def fact(j,s):
        return 1-beta(j, eps_encode[s], p);
    return sum(cnt*prod(fact(j,s) for j,s in mlt) for mlt, cnt in mults.items())

def phi_term(phi, eps, p):
    """Helper function for sum_phi_terms(), for eps = u, p.

    For eps=u:  return N_phi * prod_{1^d in phi}(1-beta(2*d, u, p))

    For eps=p:  return N_phi * prod_{1^d in phi}(1-beta(d, p, p))

    """
    i = 2 if eps == "u" else 1
    return N_phi(phi,p) * prod(1-beta(i*e,eps,p) for d,e in phi if d==1)

def sum_phi_terms(n, eps, p):
    """
    Second helper function for S(), for eps = u,p.
    NB not required for eps=u, n odd.
    """
    #print("In sum_phi_terms(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    m = n//2 if eps == "u" else n
    phis = [phi for phi in Phi(m) if phi!=[[1,m]]]
    return sum(phi_term(phi, eps, p) for phi in phis)

def S(n, eps, p=pp):
    """
    For eps=1,u,p (n even) or just 1,p (n odd):

    S(n,eps,p) = alpha(n,eps,p) - p**-(n-1) * beta(n,eps,p) (eps="u","p");
    S(n,"1",p") = alpha(n,"1", p)
    """
    #print("In S(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    if eps == "1":
        e = ((3*n+1)//2 if n%2 else 3*n//2) if p==2 else n
        return 1 - p**(-e)*sum_f_terms(n, eps, p)
    if eps == "u":
        if n%2:
            return 0
        return 1 - p**(-n) * (p + sum_f_terms(n, eps, p) + sum_phi_terms(n, eps, p))
    # now eps=="p"
    return  1 - p**(-n) * (p + sum_phi_terms(n, eps, p))

def make_alphas_and_betas(n, p=pp, verbose=False):
    """Compute (and optionally display) all alpha(i,eps,p) and and beta(i,eps,p) for i<=p.
    """
    if n<3:
        return
    k = (n,"1",p)
    if k in alpha_dict and k in beta_dict:
        if verbose:
            print("{} already in alpha_dict and beta_dict".format(k))
        return
    for i in range(3,n):
        make_alphas_and_betas(i, p, verbose)

    if verbose:
        print("Computing alpha({},eps,{}) and beta({},eps,{})".format(n,p,n,p))
    r = p**(-(n-1))
    s = p**(-binomial(n,2))
    rs = r*s

    epslist = ["1", "u", "p"]
    eps2list = ["p", "p", "1"] if n%2 else epslist
    R_n = dict([(eps,R(n,eps,p)) for eps in epslist])

    alpha_dict[(n,"1",p)] = S(n,"1",p)
    alpha_dict[(n,"u",p)] = alpha_dict[(n,"1",p)] if n%2 else (S(n,"u",p)+r*R_n["u"])/(1-rs)
    t = S(n,"p",p)+r*R_n["p"]
    alpha_dict[(n,"p",p)] = (t+rs*alpha_dict[(n,"1",p)]) if n%2 else t/(1-rs)

    for eps1, eps2 in zip(epslist, eps2list):
        beta_dict[(n,eps1,p)]  = R_n[eps1] + s*alpha_dict[(n, eps2, p)]

    if verbose:
        print("Added entries for n={} to alpha_dict and beta_dict for p={}".format(n,p))

eps_encode = {-1: "u", 0: "p", +1: "1"}
eps_decode = {"u": -1, "p": 0, "1": +1}

def alpha(n, eps, p=pp):
    #print("In alpha(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    try:
        eps = eps_encode[eps]
    except KeyError:
        pass
    if n<3:
        if eps=="1":
            return 1
        if eps=="u":
            return n if n<2 else p/(p+1)
        if eps=="p":
            return n if n<2 else 1/2
    k = (n, eps, p)
    if k not in alpha_dict:
        make_alphas_and_betas(n, p)
    return alpha_dict[k]

def beta(n, eps, p=pp):
    #print("In beta(n, eps, p) with n={}, eps={}, p={}".format(n,eps,p))
    try:
        eps = eps_encode[eps]
    except KeyError:
        pass
    if n<3:
        if eps=="1":
            return 1 if n<2 else 1/p
        if eps=="u":
            return n if n<2 else 1/(p+1)
        if eps=="p":
            return n if n<2 else 1/2
    k = (n, eps, p)
    if k not in beta_dict:
        make_alphas_and_betas(n, p)
    return beta_dict[k]

def check_value(ab,i,eps,val,p=pp):
    myval = (beta if ab=="beta" else alpha)(i,eps,p)
    symb = "{}({},{}; {})".format(ab,i,eps,p)
    if myval==val:
        print("{} OK".format(symb, p))
    else:
        print("WRONG {} = {}, should be {}".format(symb,myval,val))

def check3():
    """ Check that all 3 beta(3,eps; p) are correct for p=3 and p generic.
    """
    p = pp
    alpha_3_p_generic = (4*p**5 - p**3 + 3*p**2 - 6*p + 6)/(6*p**5)
    beta_3_1_generic = beta_3_u_generic = (6*p**7-3*p**6+p**5-p**3+3*p**2-6*p+6)/(6*p**8)
    beta_3_p_generic = (p**3+p**2-2*p+2)/(2*p**3)
    make_alphas_and_betas(3)
    check_value("alpha",3,"1", 1)
    check_value("alpha",3,"u", 1)
    check_value("alpha",3,"p", alpha_3_p_generic)
    check_value("beta",3,"1", beta_3_1_generic)
    check_value("beta",3,"u", beta_3_u_generic)
    check_value("beta",3,"p", beta_3_p_generic)

    make_alphas_and_betas(3,2)
    check_value("alpha",3,"1", 7/8, 2)
    check_value("alpha",3,"u", 7/8, 2)
    check_value("alpha",3,"p", 167/256,2)
    check_value("beta",3,"1", 807/2048, 2)
    check_value("beta",3,"u", 807/2048, 2)
    check_value("beta",3,"p", 39/64,2)

    make_alphas_and_betas(3,3)
    check_value("alpha",3,"1", 26/27, 3)
    check_value("alpha",3,"u", 26/27, 3)
    check_value("alpha",3,"p", 4319/6561,3)
    check_value("beta",3,"1", 50246/177147, 3)
    check_value("beta",3,"u", 50246/177147, 3)
    check_value("beta",3,"p", 431/729,3)

    # for p>=5 the generic formulas hold:
    make_alphas_and_betas(3,5)
    check_value("alpha",3,"1", 1, 5)
    check_value("alpha",3,"u", 1, 5)
    check_value("alpha",3,"p", subs(alpha_3_p_generic,5), 5)
    check_value("beta",3,"1", subs(beta_3_1_generic,5), 5)
    check_value("beta",3,"u", subs(beta_3_u_generic,5), 5)
    check_value("beta",3,"p", subs(beta_3_p_generic,5), 5)

def check4():
    """ Check that all 3 beta(4,eps; p) are correct for p=3, p=5 and p generic.
    """
    p = pp
    alpha_4_u_generic = p*(p-1)*(2*p**9 + 6*p**8 + 6*p**7 + 4*p**6 + 3*p**5 + 5*p**4 + 5*p**3 + 5*p**2 + 5*p + 2)/(2*(p+1)**2*(p**9-1))
    alpha_4_p_generic = (p-1)*(5*p**9 + 10*p**8 + 10*p**7 + 9*p**6 + 12*p**5 + 8*p**4 + 8*p**3 + 12*p**2 + 12*p + 4)/(8*(p + 1)*(p**9 - 1))
    beta_4_1_generic = (p**2+1)*(2*p**3-p**2-2*p+2)/(2*p**6)
    beta_4_u_generic = (2*p**10+3*p**9-p**5+2*p**4-2*p**2-3*p-1)/(2*(p+1)**2 *(p**9-1))
    beta_4_p_generic = (4*p**10+8*p**9-4*p**8+4*p**6-3*p**4+p**3-5*p-5)/(8*(p+1)*(p**9-1))

    make_alphas_and_betas(4)
    check_value("alpha",4,"1", 1)
    check_value("alpha",4,"u", alpha_4_u_generic)
    check_value("alpha",4,"p", alpha_4_p_generic)
    check_value("beta",4,"1", beta_4_1_generic)
    check_value("beta",4,"u", beta_4_u_generic)
    check_value("beta",4,"p", beta_4_p_generic)

    make_alphas_and_betas(4,2)
    check_value("alpha",4,"1", 13863/16384, 2)
    check_value("alpha",4,"u", 3832/4599, 2)
    check_value("alpha",4,"p", 1907/3066,2)
    check_value("beta",4,"1", 407079/1048576, 2)
    check_value("beta",4,"u", 3569/9198, 2)
    check_value("beta",4,"p", 7369/12264,2)

    make_alphas_and_betas(4,3)
    check_value("alpha",4,"1", 76/81, 3)
    check_value("alpha",4,"u", subs(alpha_4_u_generic,3), 3)
    check_value("alpha",4,"p", subs(alpha_4_p_generic,3), 3)
    check_value("beta",4,"1", 16600/59049, 3)
    check_value("beta",4,"u", subs(beta_4_u_generic,3), 3)
    check_value("beta",4,"p", subs(beta_4_p_generic,3), 3)

    make_alphas_and_betas(4,5)
    check_value("alpha",4,"1", 124/125, 5)
    check_value("alpha",4,"u", subs(alpha_4_u_generic,5), 5)
    check_value("alpha",4,"p", subs(alpha_4_p_generic,5), 5)
    check_value("beta",4,"1", 352624/1953125, 5)
    check_value("beta",4,"u", subs(beta_4_u_generic,5), 5)
    check_value("beta",4,"p", subs(beta_4_p_generic,5), 5)



def check5():
    """ Check that all beta(5,eps; p) and alpha(5,eps; p) are correct for p=3.
    """
    p = pp
    make_alphas_and_betas(5)
    check_value("beta",5,"1",(p**26 + 1/2*p**25 - 1/2*p**24 + 1/2*p**23 - 1/2*p**22 + p**20 - 1/2*p**19 - 11/30*p**17 + 2/15*p**16 - 1/12*p**15 + 1/6*p**14 - 3/10*p**13 + 1/5*p**12 + 1/4*p**11 - 1/3*p**7 + 1/6*p**5 - 5/6*p**3 + 3/2*p**2 + p - 1)/(p**27 + p**26))
    check_value("beta",5,"u",(p**26 + 1/2*p**25 - 1/2*p**24 + 1/2*p**23 - 1/2*p**22 + p**20 - 1/2*p**19 - 11/30*p**17 + 2/15*p**16 - 1/12*p**15 + 1/6*p**14 - 3/10*p**13 + 1/5*p**12 + 1/4*p**11 - 1/3*p**7 + 1/6*p**5 - 5/6*p**3 + 3/2*p**2 + p - 1)/(p**27 + p**26))
    check_value("beta",5,"p",(1/2*p**13 + p**12 - 1/2*p**11 + 1/2*p**9 - 1/3*p**7 + 1/6*p**5 - 5/6*p**3 + 3/2*p**2 + p - 1)/(p**13 + p**12))
    check_value("alpha",5,"1",1)
    check_value("alpha",5,"u",1)
    check_value("alpha",5,"p",  (19/30*p**17 + 19/30*p**16 - 1/12*p**15 + 1/6*p**14 - 3/10*p**13 + 1/5*p**12 + 1/4*p**11 - 1/3*p**7 + 1/6*p**5 - 5/6*p**3 + 3/2*p**2 + p - 1)/(p**17 + p**16))

    make_alphas_and_betas(5,3)
    check_value("beta",5,"p", 1493687989147/2541865828329, 3)
    check_value("beta",5,"1", 13670659773280445407/48630661836227715204, 3)
    check_value("beta",5,"u", 13670659773280445407/48630661836227715204, 3)
    check_value("alpha",5,"p", 129514464056263/205891132094649, 3)
    check_value("alpha",5,"1", 160260073/172186884, 3)
    check_value("alpha",5,"u", 160260073/172186884, 3)

def check6():
    """ Check that all beta(6,eps; p) and alpha(6,eps; p) are correct for p=3.
    """
    p = pp
    make_alphas_and_betas(6)
    check_value("alpha",6,"1",1)
    check_value("alpha",6,"u",(p**31 + 4*p**30 + 8*p**29 + 11*p**28 + 13*p**27 + 29/2*p**26 + 103/6*p**25 + 56/3*p**24 + 133/6*p**23 + 68/3*p**22 + 68/3*p**21 + 127/6*p**20 + 62/3*p**19 + 65/3*p**18 + 139/6*p**17 + 193/8*p**16 + 577/24*p**15 + 24*p**14 + 191/8*p**13 + 583/24*p**12 + 23*p**11 + 19*p**10 + 17*p**9 + 31/2*p**8 + 25/2*p**7 + 59/6*p**6 + 15/2*p**5 + 5*p**4 + 7/3*p**3 + 3/2*p**2 + 2*p + 1)/(p**31 + 4*p**30 + 8*p**29 + 12*p**28 + 16*p**27 + 20*p**26 + 24*p**25 + 28*p**24 + 32*p**23 + 35*p**22 + 36*p**21 + 36*p**20 + 36*p**19 + 36*p**18 + 36*p**17 + 36*p**16 + 36*p**15 + 36*p**14 + 36*p**13 + 36*p**12 + 35*p**11 + 32*p**10 + 28*p**9 + 24*p**8 + 20*p**7 + 16*p**6 + 12*p**5 + 8*p**4 + 4*p**3 + p**2))
    check_value("alpha",6,"p",(91/144*p**29 + 91/36*p**28 + 5*p**27 + 1075/144*p**26 + 719/72*p**25 + 37/3*p**24 + 117/8*p**23 + 427/24*p**22 + 21*p**21 + 1651/72*p**20 + 218/9*p**19 + 1169/48*p**18 + 427/18*p**17 + 1711/72*p**16 + 1159/48*p**15 + 187/8*p**14 + 545/24*p**13 + 49/2*p**12 + 26*p**11 + 101/4*p**10 + 301/12*p**9 + 95/4*p**8 + 85/4*p**7 + 223/12*p**6 + 33/2*p**5 + 29/2*p**4 + 10*p**3 + 11/2*p**2 + 5/2*p + 1/2)/(p**29 + 4*p**28 + 8*p**27 + 12*p**26 + 16*p**25 + 20*p**24 + 24*p**23 + 28*p**22 + 32*p**21 + 35*p**20 + 36*p**19 + 36*p**18 + 36*p**17 + 36*p**16 + 36*p**15 + 36*p**14 + 36*p**13 + 36*p**12 + 36*p**11 + 36*p**10 + 35*p**9 + 32*p**8 + 28*p**7 + 24*p**6 + 20*p**5 + 16*p**4 + 12*p**3 + 8*p**2 + 4*p + 1))
    check_value("beta",6,"1",(p**24 + 1/2*p**23 + 1/2*p**22 + p**21 + p**19 + p**18 + 1/2*p**17 + p**16 - 7/8*p**15 + 2/3*p**14 - 1/2*p**13 + 5/24*p**12 + 1/2*p**11 - 3/2*p**10 + 3/2*p**9 + 1/2*p**8 + 1/2*p**6 + 1/3*p**5 + 1/2*p**4 + 1/6*p**3 + 1/2*p**2 + p - 1)/(p**25 + p**24 + p**23 + p**22 + p**21 + p**20 + p**19 + p**18 + p**17))
    check_value("beta",6,"u",(p**28 + 7/2*p**27 + 6*p**26 + 17/2*p**25 + 11*p**24 + 13*p**23 + 16*p**22 + 39/2*p**21 + 45/2*p**20 + 193/8*p**19 + 577/24*p**18 + 24*p**17 + 191/8*p**16 + 583/24*p**15 + 24*p**14 + 23*p**13 + 25*p**12 + 53/2*p**11 + 51/2*p**10 + 73/3*p**9 + 71/3*p**8 + 121/6*p**7 + 37/2*p**6 + 47/3*p**5 + 41/3*p**4 + 55/6*p**3 + 14/3*p**2 + 13/6*p + 2/3)/(p**29 + 4*p**28 + 8*p**27 + 12*p**26 + 16*p**25 + 20*p**24 + 24*p**23 + 28*p**22 + 32*p**21 + 35*p**20 + 36*p**19 + 36*p**18 + 36*p**17 + 36*p**16 + 36*p**15 + 36*p**14 + 36*p**13 + 36*p**12 + 36*p**11 + 36*p**10 + 35*p**9 + 32*p**8 + 28*p**7 + 24*p**6 + 20*p**5 + 16*p**4 + 12*p**3 + 8*p**2 + 4*p + 1))
    check_value("beta",6,"p",(1/2*p**35 + 5/2*p**34 + 5*p**33 + 7*p**32 + 19/2*p**31 + 25/2*p**30 + 91/6*p**29 + 35/2*p**28 + 20*p**27 + 133/6*p**26 + 22*p**25 + 22*p**24 + 49/2*p**23 + 26*p**22 + 103/4*p**21 + 3775/144*p**20 + 473/18*p**19 + 105/4*p**18 + 3751/144*p**17 + 1907/72*p**16 + 79/3*p**15 + 177/8*p**14 + 439/24*p**13 + 33/2*p**12 + 1003/72*p**11 + 211/18*p**10 + 147/16*p**9 + 56/9*p**8 + 271/72*p**7 + 95/48*p**6 + 11/8*p**5 + 17/24*p**4 - 1/2*p - 1/2)/(p**35 + 4*p**34 + 8*p**33 + 12*p**32 + 16*p**31 + 20*p**30 + 24*p**29 + 28*p**28 + 32*p**27 + 35*p**26 + 36*p**25 + 36*p**24 + 36*p**23 + 36*p**22 + 36*p**21 + 36*p**20 + 36*p**19 + 36*p**18 + 36*p**17 + 36*p**16 + 35*p**15 + 32*p**14 + 28*p**13 + 24*p**12 + 20*p**11 + 16*p**10 + 12*p**9 + 8*p**8 + 4*p**7 + p**6))

    make_alphas_and_betas(6,3)
    check_value("alpha",6, "p", 690037935950003/1098030248972800, 3)
    check_value("alpha",6,"1", 28366779023771/30502389939948, 3)
    check_value("alpha",6,"u", 9541669997405587/10262359634630400, 3)
    check_value("beta",6,"p", 26377476341107224253/44887561041873369600, 3)
    check_value("beta",6,"1", 605398279518845051650813/2153584544086426253951538, 3)
    check_value("beta",6,"u", 27339928051320364957/97256382257392300800, 3)

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

def make_gammas_odd_iter(n,p, code="1"):
    """Read from file "gamma{n}_{p}.out" and return an iterator through
    the set Gamma(n,1) (if code=="1") or Gamma(n,u) (if code=="u"), up
    to affine transforms.
    """
    assert n%2==1
    F = GF(p)
    Fx = PolynomialRing(F, 'x')
    u = a_nonsquare(F)
    lc = a_nonsquare(F) if code=="u" else F(1)
    # We need to read the file twice when p|n or p=1 (mod 4).
    # First time (always):
    coeff_iter = read_gamma_c_output_iter(n, p, u, "gamma{}_{}.out".format(n,p), code)
    n = 0
    for coeffs in coeff_iter:
        n += 1
        if (n%1000000==0):
            print("Read {} coefficient lists".format(n))
        yield lc*Fx(coeffs)
    # Second time (conditional):
    if n%p==0 or p%4==1:
        other_code = "u" if code=="1" else "1"
        i = n-2 if p%n else n-1
        coeff_iter = read_gamma_c_output_iter(n, p, u, "gamma{}_{}.out".format(n,p), other_code)
        n = 0
        for coeffs in coeff_iter:
            n += 1
            if (n%1000000==0):
                print("Read {} coefficient lists".format(n))
                f = Fx(coeffs)
                if f[i]:
                    yield lc*scale(f,u)

Gamma_plus_mult_dict= {}
Gamma_minus_mult_dict= {}
Gamma_plus_short_mult_dict= {}
Gamma_minus_short_mult_dict= {}

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

    for code in ["1", "u"]:
        print("Reading C output with code {}".format(code))
        if n%2:
            rmc = root_multiplicity_counts(make_gammas_odd_iter(n,p, code))
        else:
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


##########################################################################################
#
# old code for computing Gamma sets of polynomials for odd p, now obsolete
#

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

def old_f_term(f,p=pp):
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

def old_sum_f_terms(flist, p=pp, mflag=False):
    """
    Sum of old_f_term(f,p) over f in flist
    """
    if p==pp: # will not be called in this case anyway
        return 0
    if mflag:
        from basics import f_multiplicity
        return sum(f_multiplicity(f)*old_f_term(f, p) for f in flist)
    else:
        return sum(old_f_term(f, p) for f in flist)

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

def lambda_helper(phi, NN, p=pp):
    """ Helper function for affine and projective factorization probabilities.
    """
    d = deg_fp(phi)
    return prod([prod([NN(j,p)-i for i in
                       range(m1(phi,j))])/prod([ZZ(m2(phi,[j,i])).factorial()
                                                for i in range(1,d+1)]) for j in range(1,d+1)])
def N_forms(j, p=pp):
    """The number of degree j homogeneous irreducibles in GF(p)[X,Y] up to scaling.
    """
    return p+1 if j==1 else N_monics(j,p)

def lambda_P(phi, p=pp):
    """ The probability that a homogeneous polynomial of degree deg(phi) has factorization pattern phi.
    """
    d = deg_fp(phi)
    return lambda_helper(phi, N_forms, p) * (p-1)/ (p**(d+1)-1)

def old_phi_term(phi, double, p, v=None):
    """Helper function for alpha(-,p), alpha(-,u).

    alpha(-,u) has double=True which uses beta(2*e,u) for (1,e) in phi.

    alpha(-,p) has double=False which uses beta(e,p) for (1,e) in phi.

    """
    be = (lambda i: beta_minus(2*i,p,v)) if double else (lambda i: beta_0(i,p,v))
    return lambda_A(phi,p) * prod(1-be(e) for d,e in phi if d==1)

def sum_old_phi_terms(i, double, p, v):
    j = i//2 if double else i
    return sum(old_phi_term(phi, double, p, v) for phi in Phi(j))

def old_alpha(i,p=pp,v=None):
    """ Average of alpha(i,1) and alpha(i,u)
    """
    return (alpha_plus(i,p,v)+alpha_minus(i,p,v))/2

def old_beta(i,p=pp,v=None):
    """ Average of beta(i,1) and beta(i,u)
    """
    return (beta_plus(i,p,v)+beta_minus(i,p,v))/2

def beta_eps(eps):
    """ Return the function beta(-,u), beta(-,p) or beta(-,1) according to eps=-1,0,+1.
    """
    try:
        return [beta_minus,beta_0,beta_plus][eps+1]
    except IndexError:
        return beta

def old_sum_f_terms_from_mults(counts_dict, p=pp):
    return sum(cnt*prod(1-beta_eps(eps)(j,p) for j,eps in mlt) for mlt, cnt in counts_dict.items())

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
        a = 1 - old_sum_f_terms_from_mults(Gamma_plus_mults(i,p), p)/p**e
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
    a = 1 - sum_old_phi_terms(i,True,p,v) / p**i2
    if p in ZZ:
        e = 3*i2 if p==2 else i
        a = a - old_sum_f_terms_from_mults(Gamma_minus_mults(i, p),p) / p**e
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
    a = 1 - sum_old_phi_terms(i,False,p,v)
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

