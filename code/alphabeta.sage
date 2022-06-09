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
        e = 3*n//2 if p==2 else n
        return 1 - p**(-n) * (p + sum_phi_terms(n, eps, p)) - p**(-e) * sum_f_terms(n, eps, p)
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
            a = (alpha(i,"1",p) + alpha(i,"u",p))/2
            b = (beta(n-i,"1",p) + beta(n-i,"u",p))/2
            return ie(a, b)
        else:
            return (ie(beta(n-i,"1",p), alpha(i,"1",p)) + ie(beta(n-i,"u",p), alpha(i,"u",p)))/2

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
        return ie(beta(n-i,"p",p), alpha(i,"p",p))
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

rho_values = {} # place-holder: value defined below

def check_rho(g,p=pp):
    """Check that rho_g is correct for g=1,2 and small p.

    Here, "correct" means "agrees with Section 2" for g=1 and "agrees
    with Tom's independent calculations" for g=2.

    """
    if g in rho_values:
        r = rho(g,p)
        rt = rho_values[g].get(p, subs(rho_values[g][pp],p))
        if r==rt:
            print("rho_{}({}) OK".format(g, p))
            return True
        else:
            print("rho_{}({}) = {} is WRONG, should be {}".format(g, p, r, rt))
            return False
    else:
        print("rho_g values only stored for g = 1, 2 so far")
        return None

def check_all_rho():
    np = {1:5, 2: 6, 3: 10, 4: 16, 5: 4, 6: 4}
    assert all(all([check_rho(g,p) for p in [pp]+primes_first_n(np[g])]) for g in range(1,7))
"""
Space for comments

"""


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

############  Precomputed generic and specific rho(g,p) ######################################

rho_values = {1: {pp:(8*pp**10+8*pp**9-4*pp**8+2*pp**6+pp**5-2*pp**4+pp**3-pp**2-8*pp-5)/(8*(pp+1)*(pp**9-1))},
              2: {pp:(pp-1)**3 * (144*pp**40 + 576*pp**39 + 1296*pp**38 + 2232*pp**37 + 3384*pp**36 + 4788*pp**35 + 6492*pp**34 + 8263*pp**33 + 10041*pp**32 + 11580*pp**31 + 12883*pp**30 + 13947*pp**29 + 14784*pp**28 + 15378*pp**27 + 15785*pp**26 + 15912*pp**25 + 15965*pp**24 + 16172*pp**23 + 16296*pp**22 + 16337*pp**21 + 16191*pp**20 + 15715*pp**19 + 15006*pp**18 + 14095*pp**17 + 12964*pp**16 + 11580*pp**15 + 9739*pp**14 + 7905*pp**13 + 6228*pp**12 + 4662*pp**11 + 3329*pp**10 + 2139*pp**9 + 1212*pp**8 + 521*pp**7 + 81*pp**6 - 36*pp**5 - 90*pp**4 - 144*pp**3 - 144*pp**2 - 144*pp - 72)/(144*pp**6 *(pp+1)*(pp**20 -1)*(pp**9 -1)*(pp**7 -1)),
                  2: 521968414037549/557460453580800,
                  3: 11908283690073923675989/12265526054691898243200,
                  5: 21168046192107392417824270157/21315998310595527294273375000,
                  7: 9225394906523129800081108647433021/9243647281033059837025942476710400,
                  11: 291968807821387146869087552918410773299321/292073047488128339469598819346962539694720},
              3: {pp: (pp**94 + 5*pp**93 + 14*pp**92 + 30*pp**91 + 109/2*pp**90 + 89*pp**89 + 541/4*pp**88 + 586/3*pp**87 + 13003/48*pp**86 + 2091161/5760*pp**85 + 677891/1440*pp**84 + 3425077/5760*pp**83 + 704003/960*pp**82 + 113753/128*pp**81 + 3050893/2880*pp**80 + 89737/72*pp**79 + 2087459/1440*pp**78 + 60077/36*pp**77 + 3654619/1920*pp**76 + 6194257/2880*pp**75 + 4625087/1920*pp**74 + 192475/72*pp**73 + 16946713/5760*pp**72 + 2310799/720*pp**71 + 555703/160*pp**70 + 1790701/480*pp**69 + 1909949/480*pp**68 + 539451/128*pp**67 + 1703729/384*pp**66 + 4461173/960*pp**65 + 27880337/5760*pp**64 + 2409049/480*pp**63 + 9945929/1920*pp**62 + 30673859/5760*pp**61 + 1744943/320*pp**60 + 83431/15*pp**59 + 10849877/1920*pp**58 + 32936647/5760*pp**57 + 16587923/2880*pp**56 + 33309167/5760*pp**55 + 8333669/1440*pp**54 + 33234037/5760*pp**53 + 6599143/1152*pp**52 + 1632245/288*pp**51 + 67027/12*pp**50 + 7898771/1440*pp**49 + 3434559/640*pp**48 + 3348077/640*pp**47 + 7308973/1440*pp**46 + 28212971/5760*pp**45 + 903497/192*pp**44 + 25899791/5760*pp**43 + 24608591/5760*pp**42 + 322671/80*pp**41 + 2178259/576*pp**40 + 6760121/1920*pp**39 + 6241657/1920*pp**38 + 2145209/720*pp**37 + 5207731/1920*pp**36 + 2350129/960*pp**35 + 1399587/640*pp**34 + 3719741/1920*pp**33 + 272157/160*pp**32 + 709769/480*pp**31 + 203177/160*pp**30 + 774113/720*pp**29 + 5163601/5760*pp**28 + 132091/180*pp**27 + 1130791/1920*pp**26 + 88735/192*pp**25 + 2025169/5760*pp**24 + 185183/720*pp**23 + 258631/1440*pp**22 + 42679/360*pp**21 + 13931/192*pp**20 + 74311/1920*pp**19 + 45241/2880*pp**18 + 4861/5760*pp**17 - 12509/1440*pp**16 - 5345/384*pp**15 - 791/48*pp**14 - 291/16*pp**13 - 113/6*pp**12 - 37/2*pp**11 - 35/2*pp**10 - 29/2*pp**9 - 139/12*pp**8 - 39/4*pp**7 - 23/3*pp**6 - 16/3*pp**5 - 11/4*pp**4 - 2/3*pp**3 + pp**2 + 2*pp + 1)/(pp**94 + 5*pp**93 + 14*pp**92 + 30*pp**91 + 55*pp**90 + 91*pp**89 + 140*pp**88 + 204*pp**87 + 285*pp**86 + 384*pp**85 + 501*pp**84 + 636*pp**83 + 789*pp**82 + 960*pp**81 + 1149*pp**80 + 1356*pp**79 + 1581*pp**78 + 1824*pp**77 + 2084*pp**76 + 2359*pp**75 + 2646*pp**74 + 2941*pp**73 + 3240*pp**72 + 3539*pp**71 + 3834*pp**70 + 4121*pp**69 + 4396*pp**68 + 4656*pp**67 + 4899*pp**66 + 5124*pp**65 + 5331*pp**64 + 5520*pp**63 + 5691*pp**62 + 5844*pp**61 + 5979*pp**60 + 6095*pp**59 + 6190*pp**58 + 6262*pp**57 + 6310*pp**56 + 6334*pp**55 + 6334*pp**54 + 6310*pp**53 + 6262*pp**52 + 6190*pp**51 + 6095*pp**50 + 5979*pp**49 + 5844*pp**48 + 5691*pp**47 + 5520*pp**46 + 5331*pp**45 + 5124*pp**44 + 4899*pp**43 + 4656*pp**42 + 4396*pp**41 + 4121*pp**40 + 3834*pp**39 + 3539*pp**38 + 3240*pp**37 + 2941*pp**36 + 2646*pp**35 + 2359*pp**34 + 2084*pp**33 + 1824*pp**32 + 1581*pp**31 + 1356*pp**30 + 1149*pp**29 + 960*pp**28 + 789*pp**27 + 636*pp**26 + 501*pp**25 + 384*pp**24 + 285*pp**23 + 204*pp**22 + 140*pp**21 + 91*pp**20 + 55*pp**19 + 30*pp**18 + 14*pp**17 + 5*pp**16 + pp**15),
                  2: 357792959367031334203330778481486352159/382068150177100056504451182727947878400,
                  3: 341947650353077734424671144337255654488619491925373857/352129923021605466157817219233951832056896259545331200,
                  5: 86097630260784435447100598782562008926113896114013014530256922666498909279/86666803123976066755869260179323358963196506650206092672348022460937500000,
                  7: 305506442225959695750731221696357847002652799121681101310512708797306578845450637/305990864147524980302408365049149826079047472404966616252928609903674358381056000,
                  11: 180381571841180908637993538515031270909180246518441013584176907296658488528568533984567035173827692691/180400743281165829494219178794411859093803084918009201007525439211677254684714957353538885664070745600,
                  13: 56436513939340864051763567947767739265217884838160058023121276435745647756489025435740351887740315083551/56438369264054703660878373727149871197122495421013146340682554818431287327790812757797626586573714226400,
                  17: 19576400522426429088568588738058180397597986892680480588688953801551407094217802927516631345885114921887863106374891/19576524741352669758651197387522637257387105112162448594248715236280289913300659213066392916414975836300436672613600,
                  19: 397080281898692114315140080468919438743491351972325483159482395965279526502566996354913055476049191986968190953590827681/397081783878981691068459885208595813525996542578822208487535509368851516269249962017698346568130230329932384249699520000,
                  23: 48522081181573083036423111208272474959156068979329498181233500364119674925899578731319060688452318413504651439449259553105848387/48522164332307575207405924988815987189118960361454063750317623708432993676808946048191915966793163268891500189935412563002675200},
              4: {pp: (pp**169 + 8*pp**168 + 34*pp**167 + 104*pp**166 + 259*pp**165 + 1119/2*pp**164 + 2177/2*pp**163 + 7819/4*pp**162 + 39559/12*pp**161 + 253615/48*pp**160 + 649187/80*pp**159 + 538162559/44800*pp**158 + 330534637/19200*pp**157 + 9664167361/403200*pp**156 + 124872329/3840*pp**155 + 17380000013/403200*pp**154 + 3222983941/57600*pp**153 + 179610161/2520*pp**152 + 17991598783/201600*pp**151 + 22179175103/201600*pp**150 + 3850743287/28800*pp**149 + 16168422821/100800*pp**148 + 10952765321/57600*pp**147 + 89905945579/403200*pp**146 + 104379463649/403200*pp**145 + 120074018551/403200*pp**144 + 27392458193/80640*pp**143 + 17222753119/44800*pp**142 + 29024998949/67200*pp**141 + 97167540313/201600*pp**140 + 8619526213/16128*pp**139 + 4750604875/8064*pp**138 + 65094250433/100800*pp**137 + 283943036759/403200*pp**136 + 308143571969/403200*pp**135 + 110963982769/134400*pp**134 + 179051082143/201600*pp**133 + 383689940479/403200*pp**132 + 409574163067/403200*pp**131 + 36306292957/33600*pp**130 + 1539723719/1344*pp**129 + 97644461111/80640*pp**128 + 257254329673/201600*pp**127 + 67585737187/50400*pp**126 + 37777385423/26880*pp**125 + 42309735161/28800*pp**124 + 44115198007/28800*pp**123 + 321194314919/201600*pp**122 + 11109379963/6720*pp**121 + 138007026403/80640*pp**120 + 356352642613/201600*pp**119 + 61206583019/33600*pp**118 + 10489891473/5600*pp**117 + 155001498263/80640*pp**116 + 793616593349/403200*pp**115 + 405521125141/201600*pp**114 + 137872850747/67200*pp**113 + 105270084683/50400*pp**112 + 61127046889/28800*pp**111 + 86806668637/40320*pp**110 + 879004440649/403200*pp**109 + 24682597351/11200*pp**108 + 448380561677/201600*pp**107 + 15059332307/6720*pp**106 + 227240886587/100800*pp**105 + 182592675539/80640*pp**104 + 228888180799/100800*pp**103 + 916726370389/403200*pp**102 + 32731234007/14400*pp**101 + 304928826847/134400*pp**100 + 911658966887/403200*pp**99 + 453545509213/201600*pp**98 + 90108105029/40320*pp**97 + 148938244589/67200*pp**96 + 221185160737/100800*pp**95 + 437210173307/201600*pp**94 + 95853162801/44800*pp**93 + 212385050099/100800*pp**92 + 119291807437/57600*pp**91 + 5120167259/2520*pp**90 + 802139404267/403200*pp**89 + 52255766653/26880*pp**88 + 382191441113/201600*pp**87 + 15496925713/8400*pp**86 + 722329529071/403200*pp**85 + 9998689621/5760*pp**84 + 676682380349/403200*pp**83 + 652743365401/403200*pp**82 + 209395074731/134400*pp**81 + 603102498433/403200*pp**80 + 96264270671/67200*pp**79 + 110344454449/80640*pp**78 + 525596018819/403200*pp**77 + 62410907389/50400*pp**76 + 236435857337/201600*pp**75 + 89285175523/80640*pp**74 + 14001063581/13440*pp**73 + 43752449093/44800*pp**72 + 40858776863/44800*pp**71 + 341990425121/403200*pp**70 + 3015716539/3840*pp**69 + 291807251749/403200*pp**68 + 66890345491/100800*pp**67 + 4880318201/8064*pp**66 + 14751498029/26880*pp**65 + 49855772689/100800*pp**64 + 7439777507/16800*pp**63 + 22678475753/57600*pp**62 + 140080494199/403200*pp**61 + 8757830717/28800*pp**60 + 35461837637/134400*pp**59 + 30481249027/134400*pp**58 + 25933690661/134400*pp**57 + 1636441021/10080*pp**56 + 5440116851/40320*pp**55 + 44604657589/403200*pp**54 + 2573194379/28800*pp**53 + 14300726887/201600*pp**52 + 4451989159/80640*pp**51 + 16914926489/403200*pp**50 + 1385906339/44800*pp**49 + 981970069/44800*pp**48 + 5911338383/403200*pp**47 + 1198788137/134400*pp**46 + 3122797/700*pp**45 + 214868887/201600*pp**44 - 295058803/201600*pp**43 - 44253719/13440*pp**42 - 2053627/450*pp**41 - 2175166493/403200*pp**40 - 13559713/2304*pp**39 - 822408677/134400*pp**38 - 354844601/57600*pp**37 - 2442974731/403200*pp**36 - 22454417/3840*pp**35 - 7991317/1440*pp**34 - 14944811/2880*pp**33 - 114877/24*pp**32 - 627667/144*pp**31 - 705119/180*pp**30 - 2497003/720*pp**29 - 1086187/360*pp**28 - 462473/180*pp**27 - 170587/80*pp**26 - 309143/180*pp**25 - 11989/9*pp**24 - 706097/720*pp**23 - 11993/18*pp**22 - 141581/360*pp**21 - 29969/180*pp**20 + 4231/360*pp**19 + 4183/30*pp**18 + 15857/72*pp**17 + 31841/120*pp**16 + 4238/15*pp**15 + 33089/120*pp**14 + 29989/120*pp**13 + 1056/5*pp**12 + 333/2*pp**11 + 487/4*pp**10 + 335/4*pp**9 + 671/12*pp**8 + 415/12*pp**7 + 103/6*pp**6 + 25/6*pp**5 - 47/12*pp**4 - 22/3*pp**3 - 7*pp**2 - 4*pp - 1)/(pp**169 + 8*pp**168 + 34*pp**167 + 104*pp**166 + 259*pp**165 + 560*pp**164 + 1092*pp**163 + 1968*pp**162 + 3333*pp**161 + 5366*pp**160 + 8278*pp**159 + 12307*pp**158 + 17711*pp**157 + 24760*pp**156 + 33728*pp**155 + 44885*pp**154 + 58489*pp**153 + 74778*pp**152 + 93963*pp**151 + 116223*pp**150 + 141702*pp**149 + 170508*pp**148 + 202713*pp**147 + 238353*pp**146 + 277428*pp**145 + 319902*pp**144 + 365703*pp**143 + 414723*pp**142 + 466818*pp**141 + 521809*pp**140 + 579485*pp**139 + 639608*pp**138 + 701920*pp**137 + 766151*pp**136 + 832027*pp**135 + 899277*pp**134 + 967638*pp**133 + 1036859*pp**132 + 1106704*pp**131 + 1176953*pp**130 + 1247400*pp**129 + 1317847*pp**128 + 1388096*pp**127 + 1457941*pp**126 + 1527162*pp**125 + 1595523*pp**124 + 1662773*pp**123 + 1728649*pp**122 + 1792880*pp**121 + 1855192*pp**120 + 1915315*pp**119 + 1972991*pp**118 + 2027982*pp**117 + 2080077*pp**116 + 2129096*pp**115 + 2174890*pp**114 + 2217338*pp**113 + 2256343*pp**112 + 2291828*pp**111 + 2323732*pp**110 + 2352006*pp**109 + 2376609*pp**108 + 2397504*pp**107 + 2414656*pp**106 + 2428033*pp**105 + 2437608*pp**104 + 2443361*pp**103 + 2445280*pp**102 + 2443361*pp**101 + 2437608*pp**100 + 2428033*pp**99 + 2414656*pp**98 + 2397504*pp**97 + 2376609*pp**96 + 2352006*pp**95 + 2323732*pp**94 + 2291828*pp**93 + 2256343*pp**92 + 2217338*pp**91 + 2174890*pp**90 + 2129096*pp**89 + 2080077*pp**88 + 2027982*pp**87 + 1972991*pp**86 + 1915315*pp**85 + 1855192*pp**84 + 1792880*pp**83 + 1728649*pp**82 + 1662773*pp**81 + 1595523*pp**80 + 1527162*pp**79 + 1457941*pp**78 + 1388096*pp**77 + 1317847*pp**76 + 1247400*pp**75 + 1176953*pp**74 + 1106704*pp**73 + 1036859*pp**72 + 967638*pp**71 + 899277*pp**70 + 832027*pp**69 + 766151*pp**68 + 701920*pp**67 + 639608*pp**66 + 579485*pp**65 + 521809*pp**64 + 466818*pp**63 + 414723*pp**62 + 365703*pp**61 + 319902*pp**60 + 277428*pp**59 + 238353*pp**58 + 202713*pp**57 + 170508*pp**56 + 141702*pp**55 + 116223*pp**54 + 93963*pp**53 + 74778*pp**52 + 58489*pp**51 + 44885*pp**50 + 33728*pp**49 + 24760*pp**48 + 17711*pp**47 + 12307*pp**46 + 8278*pp**45 + 5366*pp**44 + 3333*pp**43 + 1968*pp**42 + 1092*pp**41 + 560*pp**40 + 259*pp**39 + 104*pp**38 + 34*pp**37 + 8*pp**36 + pp**35),
                   2: 355822334697853578926806927839330680699964655654722666663431471376987365213/379963662301693068933020530359169368091737832703115744546905504981031321600,
                   3: 15854460792974503602330982116609970821445897720580933554536013371343633534106464013726664256174843/16326549944436990286916848331790201456737361337349232493288949452111255538564144731309314454517760,
                   5: 185234713760092811871544232359536981517542479049178183187550974339958850933790126330390340451977716386769436352807003356748262659106059244599/186458226437424209184404212286442574971275925830344362508910012263326189762793637515406599147564647989128161498229019343852996826171875000000,
                   7: 38780036792629286322983286603071514366821836858657891660551208713713021924236114696986046457883576201724232747720283828223944803118518526826065319/38841121742745994121799934271707412990645764121200333282416878445148068950325785639733841609151577469496746201138104416981386171954349683488768000,
                   11: 3331310008667303555540673730882695198200327214852847539212068449031575393180916934635007419872627778685143710154363339465709690611464225167238569921475960866741339365177427759164099/3331626636428289181692065215134314728915631976483842270869113193562214743241172116009867785627148561788093911635119447476688485765409456813765138509435680905196968286031763641190400,
                   13: 99112179751209412831495516264710054368360116230150208056858139726247322139128672678436006559536335880260313680610835825925672303417274202141017348928845108756144085155375203914434282789328467/99114532672365268810320699346710091795729726860535739778482674205800619492900296268058233579756996767844968682020118013456739698403322198189398129567614930076968196931077328528021747002716480,
                   17: 8543563508487995171506191370199177184566040290914042180826812985250585008588772083260327932688299083243575863237942080412580961668209279084142437087812471611487123310140179360750567255361174542598568234309121/8543577495214718339801130361754504282842768189006211252821256823932286651257914382138675573511939685090454224567954871713735157906556262890227050501007762266180705195082923413711089630913112921011196253483040,
                   19: 2628672281434294368571613798863489768878288861031822661485670661051697507719367641069661092545429933069610318054406943786945606630818737714591462770587737232836748206510761071710405094682945661671267824870057743211019/2628673591818143084572300990480671790552036906260281178897456823924269840422492301820476375755177866135754653134423242262900658194175799339067040804469100482350957153247222627545879954072616634731130054905836742400000,
                   23: 46239510916692135613458280230058900444045845210195347838405022244615176268619522593146280225381307239353939906166294057717233876098977187827241603676096955316094771192161772449326769813805247639159297117498553695637909630926660233/46239515113306698190672365725963420175596955002512264316934291532029891487383758916584760659061564210948719178984128016510216663668580157733741314383588560920946155890091856138909918346392738823158248703686983577678437882304708608,
                   29: 8518357166860676664175038316165756496391024274092262150525051341404118716146197464256453865149825100680687721755032688160577165398219846987827482976361250379492514404612572315625048083477501287527310363987698557258225649017219906248860632570217571/8518357368799671408299245596553205695499009738470628116555730917507068095635800866868480730938726737715459692741479821302035265186229523812180452854723479685221099386447843378612040880469961879787422738687679718881644388051362951958349526210600000,
                   31: 474268411512959146242692318921802013867907635037214640668932192568135216778713179662708062367353496595370842989812631075524976123675823049381106522096793592943348208796201808453601624638523155815008961349785826280041217098114755492174242126554804268737/474268419542939933280340588852959615091276070829908118418734987278047300532077027906903996742533847788558526729627281813648469631040946025365076412831031000815095139786113216611810924457522439960494650226814008657014625788917894264247132128096183910400,
                   37: 1760310120185273132302263859563690627929487733335496720574519065686193397264716126783568903700680401698988154044240768905145281575080904742073888246312584475938040657160197114684563881074980737727993220408667809388765570293631218654061994867689243639341295953433933/1760310132539185915484375562189094829133286224439010623225216330171473965763167216856512401553527128271905266050149453158905260005095128893186767994507008625908244348985927004851706452565755539812456370058916096813832564342108456347245110912876858946153260246122560},
              5: {pp: (pp**309 + 8*pp**308 + 35*pp**307 + 112*pp**306 + 294*pp**305 + 673*pp**304 + 2787/2*pp**303 + 5343/2*pp**302 + 19269/4*pp**301 + 99121/12*pp**300 + 651547/48*pp**299 + 5161061/240*pp**298 + 47515877/1440*pp**297 + 2143646384149/43545600*pp**296 + 445595769109/6220800*pp**295 + 634074003431/6220800*pp**294 + 55272420133/388800*pp**293 + 8479203959363/43545600*pp**292 + 2856206499497/10886400*pp**291 + 15165497522023/43545600*pp**290 + 9928915011269/21772800*pp**289 + 32098209643/54432*pp**288 + 2188318146871/2903040*pp**287 + 20757534300211/21772800*pp**286 + 12997417760941/10886400*pp**285 + 64510863874097/43545600*pp**284 + 472397635751/259200*pp**283 + 96850931248277/43545600*pp**282 + 58650650072341/21772800*pp**281 + 141059141615177/43545600*pp**280 + 33697579017191/8709120*pp**279 + 49991890937479/10886400*pp**278 + 23589299985361/4354560*pp**277 + 34583991222467/5443200*pp**276 + 322722728462671/43545600*pp**275 + 124824072735763/14515200*pp**274 + 432353156840993/43545600*pp**273 + 55200223138231/4838400*pp**272 + 568256046180437/43545600*pp**271 + 64715050220089/4354560*pp**270 + 29356601191193/1741824*pp**269 + 55264774645687/2903040*pp**268 + 2081987925637/97200*pp**267 + 1045588526464313/43545600*pp**266 + 1167923489959669/43545600*pp**265 + 433364549168141/14515200*pp**264 + 1442432702619739/43545600*pp**263 + 531749569843049/14515200*pp**262 + 879410351889833/21772800*pp**261 + 27619971737557/622080*pp**260 + 700792299079/14400*pp**259 + 463279176972611/8709120*pp**258 + 33668564835685/580608*pp**257 + 2745544076596709/43545600*pp**256 + 248139246963787/3628800*pp**255 + 1073851450890559/14515200*pp**254 + 99348187667867/1244160*pp**253 + 3744519339947689/43545600*pp**252 + 1341154873497637/14515200*pp**251 + 2853105133763/28800*pp**250 + 230782179412577/2177280*pp**249 + 4928505363376879/43545600*pp**248 + 1750745300279707/14515200*pp**247 + 1862184694489499/14515200*pp**246 + 741393007924321/5443200*pp**245 + 1047608994455701/7257600*pp**244 + 6649700929352041/43545600*pp**243 + 877858684435609/5443200*pp**242 + 1234119251522177/7257600*pp**241 + 974345751937519/5443200*pp**240 + 4096260832099591/21772800*pp**239 + 8597459921260127/43545600*pp**238 + 4504517118221969/21772800*pp**237 + 3142225427505553/14515200*pp**236 + 1969959657843371/8709120*pp**235 + 2569448596677479/10886400*pp**234 + 142800562747991/580608*pp**233 + 464412711814411/1814400*pp**232 + 1287192654135301/4838400*pp**231 + 83512983217087/302400*pp**230 + 1039053505926299/3628800*pp**229 + 43041252558233/145152*pp**228 + 6678195179515703/21772800*pp**227 + 172500031679263/544320*pp**226 + 4747508537751047/14515200*pp**225 + 699203480579653/2073600*pp**224 + 315032468237353/907200*pp**223 + 115234792579541/322560*pp**222 + 1998500633400563/5443200*pp**221 + 2051850414685429/5443200*pp**220 + 80173407987623/207360*pp**219 + 17252168544220147/43545600*pp**218 + 17661394243626673/43545600*pp**217 + 1128964491474557/2721600*pp**216 + 4614406746600913/10886400*pp**215 + 2355416436933541/5443200*pp**214 + 6406635044382779/14515200*pp**213 + 6528905585311411/14515200*pp**212 + 2849020835778811/6220800*pp**211 + 20288580852520609/43545600*pp**210 + 5155606258609363/10886400*pp**209 + 349068207718981/725760*pp**208 + 21253008815512709/43545600*pp**207 + 21548614792287791/43545600*pp**206 + 21830367068708503/43545600*pp**205 + 22097742431802679/43545600*pp**204 + 5587558624163363/10886400*pp**203 + 209142203176513/403200*pp**202 + 22808650630503163/43545600*pp**201 + 23013675217584859/43545600*pp**200 + 859334074343089/1612800*pp**199 + 1947775637627719/3628800*pp**198 + 23527188157047727/43545600*pp**197 + 7887782310598739/14515200*pp**196 + 2378149933386847/4354560*pp**195 + 23881400729456003/43545600*pp**194 + 5990710915943471/10886400*pp**193 + 750801807791831/1360800*pp**192 + 1146176678068709/2073600*pp**191 + 803163651596989/1451520*pp**190 + 4016866490949733/7257600*pp**189 + 24088565454823739/43545600*pp**188 + 2673003709189853/4838400*pp**187 + 24006670980390473/43545600*pp**186 + 11968791391368089/21772800*pp**185 + 4769982098336809/8709120*pp**184 + 11871918291802781/21772800*pp**183 + 7873193780299789/14515200*pp**182 + 1467337526542213/2721600*pp**181 + 2590842846746257/4838400*pp**180 + 2571162315056593/4838400*pp**179 + 7648793801744161/14515200*pp**178 + 1623980739480187/3110400*pp**177 + 2813614863365543/5443200*pp**176 + 22266386620157107/43545600*pp**175 + 11004296979341923/21772800*pp**174 + 1811335186738583/3628800*pp**173 + 612833572461181/1244160*pp**172 + 881190620545567/1814400*pp**171 + 6944920806553609/14515200*pp**170 + 20508293668469177/43545600*pp**169 + 28813915524431/62208*pp**168 + 6606563451603253/14515200*pp**167 + 19458741073764691/43545600*pp**166 + 19087504645720607/43545600*pp**165 + 1870660685839637/4354560*pp**164 + 4579169860888327/10886400*pp**163 + 3583672685227241/8709120*pp**162 + 1945812017566691/4838400*pp**161 + 3419834399460151/8709120*pp**160 + 16679620664585693/43545600*pp**159 + 290255799644689/777600*pp**158 + 1318663389192131/3628800*pp**157 + 5129736928668167/14515200*pp**156 + 14950759252501861/43545600*pp**155 + 14509297758138899/43545600*pp**154 + 14065521655041967/43545600*pp**153 + 6810063604004329/21772800*pp**152 + 6586905903189049/21772800*pp**151 + 2121211760709761/7257600*pp**150 + 1754457056247679/6220800*pp**149 + 11836290715736159/43545600*pp**148 + 316478612301301/1209600*pp**147 + 1825449450012221/7257600*pp**146 + 87627994067959/362880*pp**145 + 3360624525466099/14515200*pp**144 + 2413221298236907/10886400*pp**143 + 9229024581493259/43545600*pp**142 + 419567003411663/2073600*pp**141 + 279970896514439/1451520*pp**140 + 1332376037799787/7257600*pp**139 + 63307065010067/362880*pp**138 + 171605467499893/1036800*pp**137 + 22755016331405/145152*pp**136 + 6454549328798617/43545600*pp**135 + 3046003656574273/21772800*pp**134 + 637698981574999/4838400*pp**133 + 1349194650246503/10886400*pp**132 + 5064814913386189/43545600*pp**131 + 4743710329897573/43545600*pp**130 + 2216867298753479/21772800*pp**129 + 1378373279849197/14515200*pp**128 + 962014587973657/10886400*pp**127 + 893175665754857/10886400*pp**126 + 551527506128383/7257600*pp**125 + 1528758767201297/21772800*pp**124 + 313087887209507/4838400*pp**123 + 28777507227583/483840*pp**122 + 74188121989291/1360800*pp**121 + 2169834686195777/43545600*pp**120 + 43939823469049/967680*pp**119 + 85534540250431/2073600*pp**118 + 406607870809199/10886400*pp**117 + 10483371280399/311040*pp**116 + 439892147163989/14515200*pp**115 + 394048165536659/14515200*pp**114 + 30135643238603/1244160*pp**113 + 312377394205991/14515200*pp**112 + 25903799297077/1360800*pp**111 + 81079923559177/4838400*pp**110 + 639114745205087/43545600*pp**109 + 556683538879487/43545600*pp**108 + 401659687549/36288*pp**107 + 207298892009743/21772800*pp**106 + 59009461563359/7257600*pp**105 + 299924512668779/43545600*pp**104 + 251758962677647/43545600*pp**103 + 209123771417783/43545600*pp**102 + 706133381211/179200*pp**101 + 27747901342901/8709120*pp**100 + 13770712693729/5443200*pp**99 + 85479483631357/43545600*pp**98 + 3062267740273/2073600*pp**97 + 23147929634783/21772800*pp**96 + 3456452229949/4838400*pp**95 + 2632672543289/6220800*pp**94 + 7964113119113/43545600*pp**93 - 111511116443/8709120*pp**92 - 1055023855063/6220800*pp**91 - 637356436361/2177280*pp**90 - 8425935491593/21772800*pp**89 - 15536645923/34020*pp**88 - 22019774735597/43545600*pp**87 - 2599869080723/4838400*pp**86 - 12077054291821/21772800*pp**85 - 24399866989363/43545600*pp**84 - 3029483125429/5443200*pp**83 - 7915966545593/14515200*pp**82 - 5752205303123/10886400*pp**81 - 2207882598787/4354560*pp**80 - 4201672618919/8709120*pp**79 - 22143272653/48600*pp**78 - 9304653630949/21772800*pp**77 - 17343801600673/43545600*pp**76 - 1004167462763/2721600*pp**75 - 14795527214581/43545600*pp**74 - 1693151895929/5443200*pp**73 - 4109037494621/14515200*pp**72 - 1239030264821/4838400*pp**71 - 1650267761/7168*pp**70 - 1381771729/6720*pp**69 - 7352798099/40320*pp**68 - 6471658793/40320*pp**67 - 627654873/4480*pp**66 - 58164311/480*pp**65 - 74684129/720*pp**64 - 126365603/1440*pp**63 - 105427031/1440*pp**62 - 6306439/105*pp**61 - 486583603/10080*pp**60 - 380976097/10080*pp**59 - 57602921/2016*pp**58 - 103536793/5040*pp**57 - 15271521/1120*pp**56 - 311247/40*pp**55 - 9723733/3360*pp**54 + 69898/63*pp**53 + 21729233/5040*pp**52 + 34347587/5040*pp**51 + 43886449/5040*pp**50 + 101452721/10080*pp**49 + 110560109/10080*pp**48 + 115853327/10080*pp**47 + 8436277/720*pp**46 + 29465603/2520*pp**45 + 16506071/1440*pp**44 + 111623957/10080*pp**43 + 21266491/2016*pp**42 + 3124162/315*pp**41 + 18579605/2016*pp**40 + 4062461/480*pp**39 + 5162503/672*pp**38 + 34690417/5040*pp**37 + 273941/45*pp**36 + 17882059/3360*pp**35 + 46305773/10080*pp**34 + 39501989/10080*pp**33 + 16648967/5040*pp**32 + 329231/120*pp**31 + 107719/48*pp**30 + 144451/80*pp**29 + 114433/80*pp**28 + 33341/30*pp**27 + 49969/60*pp**26 + 47363/80*pp**25 + 92771/240*pp**24 + 17063/80*pp**23 + 1813/24*pp**22 - 1253/40*pp**21 - 901/8*pp**20 - 1719/10*pp**19 - 8491/40*pp**18 - 4583/20*pp**17 - 4531/20*pp**16 - 1697/8*pp**15 - 941/5*pp**14 - 1291/8*pp**13 - 7987/60*pp**12 - 311/3*pp**11 - 151/2*pp**10 - 593/12*pp**9 - 365/12*pp**8 - 109/6*pp**7 - 113/12*pp**6 - 15/4*pp**5 + 7/12*pp**4 + 10/3*pp**3 + 4*pp**2 + 3*pp + 1)/(pp**309 + 8*pp**308 + 35*pp**307 + 112*pp**306 + 294*pp**305 + 673*pp**304 + 1394*pp**303 + 2675*pp**302 + 4831*pp**301 + 8300*pp**300 + 13670*pp**299 + 21708*pp**298 + 33391*pp**297 + 49939*pp**296 + 72848*pp**295 + 103922*pp**294 + 145305*pp**293 + 199513*pp**292 + 269467*pp**291 + 358526*pp**290 + 470517*pp**289 + 609761*pp**288 + 781095*pp**287 + 989891*pp**286 + 1242071*pp**285 + 1544115*pp**284 + 1903060*pp**283 + 2326489*pp**282 + 2822511*pp**281 + 3399735*pp**280 + 4067239*pp**279 + 4834532*pp**278 + 5711508*pp**277 + 6708393*pp**276 + 7835688*pp**275 + 9104110*pp**274 + 10524530*pp**273 + 12107907*pp**272 + 13865217*pp**271 + 15807378*pp**270 + 17945174*pp**269 + 20289178*pp**268 + 22849673*pp**267 + 25636570*pp**266 + 28659325*pp**265 + 31926859*pp**264 + 35447483*pp**263 + 39228829*pp**262 + 43277786*pp**261 + 47600441*pp**260 + 52202027*pp**259 + 57086880*pp**258 + 62258406*pp**257 + 67719056*pp**256 + 73470307*pp**255 + 79512648*pp**254 + 85845571*pp**253 + 92467568*pp**252 + 99376133*pp**251 + 106567768*pp**250 + 114037992*pp**249 + 121781354*pp**248 + 129791452*pp**247 + 138060959*pp**246 + 146581655*pp**245 + 155344462*pp**244 + 164339482*pp**243 + 173556039*pp**242 + 182982726*pp**241 + 192607456*pp**240 + 202417512*pp**239 + 212399594*pp**238 + 222539863*pp**237 + 232823984*pp**236 + 243237171*pp**235 + 253764232*pp**234 + 264389613*pp**233 + 275097440*pp**232 + 285871560*pp**231 + 296695585*pp**230 + 307552939*pp**229 + 318426906*pp**228 + 329300676*pp**227 + 340157386*pp**226 + 350980157*pp**225 + 361752128*pp**224 + 372456487*pp**223 + 383076498*pp**222 + 393595521*pp**221 + 403997025*pp**220 + 414264598*pp**219 + 424381958*pp**218 + 434332966*pp**217 + 444101639*pp**216 + 453672161*pp**215 + 463028894*pp**214 + 472156392*pp**213 + 481039421*pp**212+ 489662984*pp**211 + 498012346*pp**210 + 506073057*pp**209 + 513830975*pp**208 + 521272293*pp**207 + 528383572*pp**206 + 535151778*pp**205 + 541564321*pp**204 + 547609094*pp**203 + 553274513*pp**202 + 558549561*pp**201 + 563423836*pp**200 + 567887601*pp**199 + 571931832*pp**198 + 575548263*pp**197 + 578729429*pp**196 + 581468707*pp**195 + 583760354*pp**194 + 585599539*pp**193 + 586982367*pp**192 + 587905897*pp**191 + 588368157*pp**190 + 588368157*pp**189 + 587905897*pp**188 + 586982367*pp**187 + 585599539*pp**186 + 583760354*pp**185 + 581468707*pp**184 + 578729429*pp**183 + 575548263*pp**182 + 571931832*pp**181 + 567887601*pp**180 + 563423836*pp**179 + 558549561*pp**178 + 553274513*pp**177 + 547609094*pp**176 + 541564321*pp**175 + 535151778*pp**174 + 528383572*pp**173 + 521272293*pp**172 + 513830975*pp**171 + 506073057*pp**170 + 498012346*pp**169 + 489662984*pp**168 + 481039421*pp**167 + 472156392*pp**166 + 463028894*pp**165 + 453672161*pp**164 + 444101639*pp**163 + 434332966*pp**162 + 424381958*pp**161 + 414264598*pp**160 + 403997025*pp**159 + 393595521*pp**158 + 383076498*pp**157 + 372456487*pp**156 + 361752128*pp**155 + 350980157*pp**154 + 340157386*pp**153 + 329300676*pp**152 + 318426906*pp**151 + 307552939*pp**150 + 296695585*pp**149 + 285871560*pp**148 + 275097440*pp**147 + 264389613*pp**146 + 253764232*pp**145 + 243237171*pp**144 + 232823984*pp**143 + 222539863*pp**142 + 212399594*pp**141 + 202417512*pp**140 + 192607456*pp**139 + 182982726*pp**138 + 173556039*pp**137 + 164339482*pp**136 + 155344462*pp**135 + 146581655*pp**134 + 138060959*pp**133 + 129791452*pp**132 + 121781354*pp**131 + 114037992*pp**130 + 106567768*pp**129 + 99376133*pp**128 + 92467568*pp**127 + 85845571*pp**126 + 79512648*pp**125 + 73470307*pp**124 + 67719056*pp**123 + 62258406*pp**122 + 57086880*pp**121 + 52202027*pp**120 + 47600441*pp**119 + 43277786*pp**118 + 39228829*pp**117 + 35447483*pp**116 + 31926859*pp**115 + 28659325*pp**114 + 25636570*pp**113 + 22849673*pp**112 + 20289178*pp**111 + 17945174*pp**110 + 15807378*pp**109 + 13865217*pp**108 + 12107907*pp**107 + 10524530*pp**106 + 9104110*pp**105 + 7835688*pp**104 + 6708393*pp**103 + 5711508*pp**102 + 4834532*pp**101 + 4067239*pp**100 + 3399735*pp**99 + 2822511*pp**98 + 2326489*pp**97 + 1903060*pp**96 + 1544115*pp**95 + 1242071*pp**94 + 989891*pp**93 + 781095*pp**92 + 609761*pp**91 + 470517*pp**90 + 358526*pp**89 + 269467*pp**88 + 199513*pp**87 + 145305*pp**86 + 103922*pp**85 + 72848*pp**84 + 49939*pp**83 + 33391*pp**82 + 21708*pp**81 + 13670*pp**80 + 8300*pp**79 + 4831*pp**78 + 2675*pp**77 + 1394*pp**76 + 673*pp**75 + 294*pp**74 + 112*pp**73 + 35*pp**72 + 8*pp**71 + pp**70),
                  2: 460715640303288356014699689965731953202797921191991100626740506915865518347889685271862945416108052202127450344509553450081863011717472951/491973619593763720459263314372430678158457089136395614222041282573286181158116351179168759602669616687486357047127220920993095027261440000,
                  3: 151945062515662969772674862121041669903750824592222454729757209442586497959909158791850012003604198730776790066879532307608449714862817580005909509931811001278539015404035994971560334027/156469443058414710046148987965895981096445906773520877784330159546831035838446549411828124119623598495958443849366452592968644150627747140288566661529681079275249631006158068920238080000,
                  5: 1266676046233574517674555486747279328733423925504328777695911354098368905157127071198676010715315285871405315754473500189195484328290990555642217747957537108242899491403447153495784671239120264142929278529014790002105898714640103922977626224693849668058998816470983/1275042675831175520203734119517189773624934271372271706708114295264041913002638572908412678416085426660611270494408587786324507242933934212801655532729393407641750211603024088646492974305137137660784391353894373253782812405177082837326452136039733886718750000000000,
                  7: 120807086335564138689507731521837356671590836911917217560137999659600899679143568808979214353055634990647107245148623303581825616199534550020073212321679176495521743205917187640452043343917673875135413942885091832415715532205901814464485194586696768494234657721501959287/120997366090220661744612444491160336841735251236146171814040179271382288386800773865376426474535189321802486905527740738078377403231926681654834790469580170111519433987763014712891287250918178014250766221980252696407047879168034505787055428682541530277215289278464000000},
              6: {pp: (pp**462 + 10*pp**461 + 53*pp**460 + 201*pp**459 + 616*pp**458 + 1626*pp**457 + 3841*pp**456 + 16649/2*pp**455 + 33673/2*pp**454 + 128657/4*pp**453 + 702661/12*pp**452 + 1636257/16*pp**451 + 41339071/240*pp**450 + 404587469/1440*pp**449 + 1496508529/3360*pp**448 + 4614705043352867/6706022400*pp**447 + 774026413478627/745113600*pp**446 + 5148141257570077/3353011200*pp**445 + 7463626814572051/3353011200*pp**444 + 7087032195007537/2235340800*pp**443 + 3724038759663287/838252800*pp**442 + 321263814184121/52390800*pp**441 + 7995899870329043/958003200*pp**440 + 8355414406155307/745113600*pp**439 + 277259181541169/18627840*pp**438 + 65495590225364461/3353011200*pp**437 + 170090742007220173/6706022400*pp**436 + 18222291734949037/558835200*pp**435 + 69622045394495311/1676505600*pp**434 + 175771903773744097/3353011200*pp**433 + 611196492761297/9313920*pp**432 + 2168708816438447/26611200*pp**431 + 96233080502951003/958003200*pp**430 + 11450029084128347/93139200*pp**429 + 200416413703031311/1341204480*pp**428 + 403398599787485671/2235340800*pp**427 + 363134085114841963/1676505600*pp**426 + 54161360200313209/209563200*pp**425 + 25387652836547801/82790400*pp**424 + 1213412193094995391/3353011200*pp**423 + 949754738380790579/2235340800*pp**422 + 7548264075580391/15206400*pp**421 + 1290225386344418347/2235340800*pp**420 + 67885493080281379/101606400*pp**419 + 1032756743551470761/1341204480*pp**418 + 1975526677103753293/2235340800*pp**417 + 6774874341610741913/6706022400*pp**416 + 551060933148326959/479001600*pp**415 + 1750565313389644331/1341204480*pp**414 + 4947604357178190649/3353011200*pp**413 + 79632114466222823/47900160*pp**412 + 1251924610350803899/670602240*pp**411 + 20761564546621105/9934848*pp**410 + 2606590129209084463/1117670400*pp**409 + 1450192568697068701/558835200*pp**408 + 2758421474741266723/958003200*pp**407 + 1780499574819801317/558835200*pp**406 + 23579909736952283933/6706022400*pp**405 + 2163088978014345863/558835200*pp**404 + 14251863954738050141/3353011200*pp**403 + 1951625893823656513/419126400*pp**402 + 5688315837348906469/1117670400*pp**401 + 265865439028252871/47900160*pp**400 + 10126352105482986749/1676505600*pp**399 + 21994007660157011503/3353011200*pp**398 + 4334011589563047191/609638400*pp**397 + 1909949581333340153/248371200*pp**396 + 18558724853128500589/2235340800*pp**395 + 30000538359918697807/3353011200*pp**394 + 10757898083994390097/1117670400*pp**393 + 385104675104008973/37255680*pp**392 + 24772948087331691997/2235340800*pp**391 + 11364353083120694389/958003200*pp**390 + 3542352273075844339/279417600*pp**389 + 45359586434627744273/3353011200*pp**388 + 8055053989954653079/558835200*pp**387 + 9349321574238244999/609638400*pp**386 + 6070340612828112463/372556800*pp**385 + 19322057951422659463/1117670400*pp**384 + 122841733037946437017/6706022400*pp**383 + 2321329603438379207/119750400*pp**382 + 27478063487921721539/1341204480*pp**381 + 145028733677722211267/6706022400*pp**380 + 152908755138205817347/6706022400*pp**379 + 23004151345386640823/958003200*pp**378 + 169387955106296609549/6706022400*pp**377 + 88991692264079608433/3353011200*pp**376 + 132679635671722477/4762800*pp**375 + 195873801904158221563/6706022400*pp**374 + 68387624097345039691/2235340800*pp**373 + 214676648951123836913/6706022400*pp**372 + 1753213223473768967/52390800*pp**371 + 5859065440991493323/167650560*pp**370 + 3704940839280152039/101606400*pp**369 + 5097937155085583185/134120448*pp**368 + 88489900137758437277/2235340800*pp**367 + 276239085669053498989/6706022400*pp**366 + 2871991464952004221/67060224*pp**365 + 59668737932384999639/1341204480*pp**364 + 103222066461603215143/2235340800*pp**363 + 321159842825773765859/6706022400*pp**362 + 16640873742728870527/335301120*pp**361 + 7832537367196994183/152409600*pp**360 + 89148649883461106567/1676505600*pp**359 + 2508151686100945399/45619200*pp**358 + 95233603489221211589/1676505600*pp**357 + 16387264602452098493/279417600*pp**356 + 202884624648645637037/3353011200*pp**355 + 5433116957763690071/87091200*pp**354 + 215513641113089404027/3353011200*pp**353 + 443791524106131567319/6706022400*pp**352 + 456632976957243216971/6706022400*pp**351 + 469541704990333258193/6706022400*pp**350 + 1675373645368885621/23284800*pp**349 + 247760224906281742477/3353011200*pp**348 + 508569859737234045533/6706022400*pp**347 + 86940895456246604897/1117670400*pp**346 + 267368219325955403771/3353011200*pp**345 + 996058988831644195/12192768*pp**344 + 80131818588636029857/958003200*pp**343 + 28699830577490166319/335301120*pp**342 + 117408678174537000467/1341204480*pp**341 + 2182008631092705389/24385536*pp**340 + 17514653718534504493/191600640*pp**339 + 625914257074031222597/6706022400*pp**338 + 17742941172260510557/186278400*pp**337 + 108582861993221121043/1117670400*pp**336 + 664157585791033740977/6706022400*pp**335 + 676716626746413664151/6706022400*pp**334 + 98451977461914111823/958003200*pp**333 + 14614350455768700487/139708800*pp**332 + 713681194904816095997/6706022400*pp**331 + 725730627991849932619/6706022400*pp**330 + 737626820995418591911/6706022400*pp**329 + 15293051140685792233/136857600*pp**328 + 760918443823849483069/6706022400*pp**327 + 257431140473731998181/2235340800*pp**326 + 10446323359433040571/89413632*pp**325 + 794450776166243721461/6706022400*pp**324 + 10457309956540224137/87091200*pp**323 + 815750432853379752629/6706022400*pp**322 + 275351142299736725071/2235340800*pp**321 + 836111854700802215231/6706022400*pp**320 + 281971928613636750551/2235340800*pp**319 + 122207909716887108577/958003200*pp**318 + 7861098596995627657/60963840*pp**317 + 873702576734395891627/6706022400*pp**316 + 98043450323376339179/745113600*pp**315 + 148462819951958392061/1117670400*pp**314 + 2340757811539239629/17463600*pp**313 + 302201439198007735829/2235340800*pp**312 + 914028123792561703307/6706022400*pp**311 + 460556959755778179689/3353011200*pp**310 + 103094831286840116587/745113600*pp**309 + 46711944273905678921/335301120*pp**308 + 940262530220330478397/6706022400*pp**307 + 52550953444056703997/372556800*pp**306 + 59449743656257384513/419126400*pp**305 + 39837177095406807899/279417600*pp**304 + 480300069766314051953/3353011200*pp**303 + 964713921700523558387/6706022400*pp**302 + 242107100996671399999/1676505600*pp**301 + 194347772452794474037/1341204480*pp**300 + 54146725469758562843/372556800*pp**299 + 122141406763634427451/838252800*pp**298 + 40800259319403908119/279417600*pp**297 + 23353887264965026219/159667200*pp**296 + 98210020994260215989/670602240*pp**295 + 3071610729511750207/20956320*pp**294 + 36418809612835064851/248371200*pp**293 + 983276964503508913757/6706022400*pp**292 + 982822780397899283729/6706022400*pp**291 + 981945895253221031369/6706022400*pp**290 + 65376496817011775749/447068160*pp**289 + 44496779341243170779/304819200*pp**288 + 195358642964704235927/1341204480*pp**287 + 6958874557662909887/47900160*pp**286 + 5995556293431052427/41395200*pp**285 + 967910079031477109887/6706022400*pp**284 + 48206831941038071599/335301120*pp**283 + 479982303208091165441/3353011200*pp**282 + 955399255883377296679/6706022400*pp**281 + 190089261587135987311/1341204480*pp**280 + 26253108585496864241/186278400*pp**279 + 17396344624438384747/124185600*pp**278 + 37333013566003853149/268240896*pp**277 + 11034373587097506199/79833600*pp**276 + 920096349275932675993/6706022400*pp**275 + 456480078878669619899/3353011200*pp**274 + 905486998629570122399/6706022400*pp**273 + 89768531659983587639/670602240*pp**272 + 32946806812109339257/248371200*pp**271 + 440565637901642313901/3353011200*pp**270 + 32310994276462701623/248371200*pp**269 + 53960606551161703559/419126400*pp**268 + 854059204624288271009/6706022400*pp**267 + 844474815752353724377/6706022400*pp**266 + 139104352535147761739/1117670400*pp**265 + 824522770152282127331/6706022400*pp**264 + 814174525560198357703/6706022400*pp**263 + 401795597716463438443/3353011200*pp**262 + 792782655685211558363/6706022400*pp**261 + 390879420895619373673/3353011200*pp**260 + 81074257512744287/705600*pp**259 + 379552700794237182271/3353011200*pp**258 + 29899836448676099525/268240896*pp**257 + 735711420217599080699/6706022400*pp**256 + 60313511175554559683/558835200*pp**255 + 847212285035832629/7983360*pp**254 + 31791377496671043163/304819200*pp**253 + 57252373726161810761/558835200*pp**252 + 42157707349860793711/419126400*pp**251 + 165476332346776331437/1676505600*pp**250 + 107338808730858203/1108800*pp**249 + 26515555593724231487/279417600*pp**248 + 311740353730449924107/3353011200*pp**247 + 152629502515319736979/1676505600*pp**246 + 4149278217011934107/46569600*pp**245 + 41744694771878766889/479001600*pp**244 + 51937989625343120407/609638400*pp**243 + 558183439391751161143/6706022400*pp**242 + 272516641909943302639/3353011200*pp**241 + 88646382208358876471/1117670400*pp**240 + 2646578083688529493/34214400*pp**239 + 505597096532139689071/6706022400*pp**238 + 164164123998819624107/2235340800*pp**237 + 159808578712226381401/2235340800*pp**236 + 607301659526501503/8731800*pp**235 + 25191585243401770559/372556800*pp**234 + 20978976390344061857/319334400*pp**233 + 106936898768517019537/1676505600*pp**232 + 25939101571667293253/419126400*pp**231 + 80480440130913888859/1341204480*pp**230 + 27849050099397929893/479001600*pp**229 + 5898254174780742959/104781600*pp**228 + 91303946447242689211/1676505600*pp**227 + 176538941995077833849/3353011200*pp**226 + 12632700590012590471/248371200*pp**225 + 27436579531275352043/558835200*pp**224 + 79388445994607688691/1676505600*pp**223 + 306034892974364465533/6706022400*pp**222 + 147344734534949923877/3353011200*pp**221 + 283524393258419987357/6706022400*pp**220 + 54509246747577633527/1341204480*pp**219 + 37394462985466324169/958003200*pp**218 + 4651395203975377519/124185600*pp**217 + 240794133344416180451/6706022400*pp**216 + 230622886272953234077/6706022400*pp**215 + 955266366255694217/29030400*pp**214 + 19175423206038732893/609638400*pp**213 + 100708250595523400987/3353011200*pp**212 + 64043652178668030161/2235340800*pp**211 + 183076552996880778911/6706022400*pp**210 + 174256460225634603017/6706022400*pp**209 + 82836740738280985579/3353011200*pp**208 + 13110837300317692517/558835200*pp**207 + 37307052822334701853/1676505600*pp**206 + 47123215203268587767/2235340800*pp**205 + 6687782044259466947/335301120*pp**204 + 1404301138101074839/74511360*pp**203 + 9938712410547942247/558835200*pp**202 + 37462703332378373389/2235340800*pp**201 + 11750836413014332549/745113600*pp**200 + 19874431682546920379/1341204480*pp**199 + 93230975845876833427/6706022400*pp**198 + 87332576542002216409/6706022400*pp**197 + 20418795579826637023/1676505600*pp**196 + 7625664590954600419/670602240*pp**195 + 923044913789084483/87091200*pp**194 + 6011432490971739569/609638400*pp**193 + 6823037578701330529/745113600*pp**192 + 5174151079381580459/609638400*pp**191 + 1504196172960075467/191600640*pp**190 + 2699820955674182951/372556800*pp**189 + 44760921954221288447/6706022400*pp**188 + 10283635928138796689/1676505600*pp**187 + 18856308891385240609/3353011200*pp**186 + 11496622147175233499/2235340800*pp**185 + 314607760913430781/67060224*pp**184 + 1192483901440971721/279417600*pp**183 + 927158824268680207/239500800*pp**182 + 96613850908314829/27596800*pp**181 + 21163499683045368329/6706022400*pp**180 + 594157571773986617/209563200*pp**179 + 2127408768872788307/838252800*pp**178 + 2529260893154182147/1117670400*pp**177 + 13475240280585019753/6706022400*pp**176 + 49018765008175617/27596800*pp**175 + 3492589040331448657/2235340800*pp**174 + 208343303758721107/152409600*pp**173 + 81355529466697867/68428800*pp**172 + 1722073542621722047/1676505600*pp**171 + 369178275774408197/419126400*pp**170 + 2511002235281580547/3353011200*pp**169 + 528419875643717951/838252800*pp**168 + 293055459389542427/558835200*pp**167 + 961278955485010579/2235340800*pp**166 + 5185196824174033/14968800*pp**165 + 166214154925382869/609638400*pp**164 + 12912168489328261/62092800*pp**163 + 508094448238429277/3353011200*pp**162 + 137673842000304493/1341204480*pp**161 + 26383049171387/435456*pp**160 + 82742063467756549/3353011200*pp**159 - 3829951112562361/670602240*pp**158 - 3317530467328603/106444800*pp**157 - 43788731475865951/838252800*pp**156 - 465623068663000289/6706022400*pp**155 - 558083231117331343/6706022400*pp**154 - 630564169787562931/6706022400*pp**153 - 342841465587877687/3353011200*pp**152 - 11520786141519323/106444800*pp**151 - 753077071217184319/6706022400*pp**150 - 769395179724396773/6706022400*pp**149 - 38823071783722981/335301120*pp**148 - 258591818418002191/2235340800*pp**147 - 384326870719739617/3353011200*pp**146 - 189060988980096781/1676505600*pp**145 - 49302814106357927/447068160*pp**144 - 719406619792736209/6706022400*pp**143 - 2369287900614377/22809600*pp**142 - 2741460947650657/27371520*pp**141 - 35844141115310419/372556800*pp**140 - 9650359519824361/104781600*pp**139 - 294657007121977151/3353011200*pp**138 - 56057596583057479/670602240*pp**137 - 3544437641835575/44706816*pp**136 - 55866096355080551/745113600*pp**135 - 118534689856844273/1676505600*pp**134 - 222922000662573101/3353011200*pp**133 - 59718971171840107/958003200*pp**132 - 130269395307763157/2235340800*pp**131 - 182128390366561003/3353011200*pp**130 - 42306396182409697/838252800*pp**129 - 104484595005005507/2235340800*pp**128 - 144658643642084989/3353011200*pp**127 - 7391301536616209/186278400*pp**126 - 81267026429994893/2235340800*pp**125 - 963162202920373/29030400*pp**124 - 13675556872309/453600*pp**123 - 131952575020639/4838400*pp**122 - 89081930557843/3628800*pp**121 - 103855440197/4725*pp**120 - 277351810969/14175*pp**119 - 6280276543973/362880*pp**118 - 3064319292919/201600*pp**117 - 1334958911143/100800*pp**116 - 553259608145/48384*pp**115 - 35452395190543/3628800*pp**114 - 664812919843/80640*pp**113 - 777164459599/113400*pp**112 - 3381749044361/604800*pp**111 - 646366089623/145152*pp**110 - 1037739745169/302400*pp**109 - 3049352121091/1209600*pp**108 - 6220674786211/3628800*pp**107 - 3646066895273/3628800*pp**106 - 116629324937/302400*pp**105 + 543079221551/3628800*pp**104 + 551437079357/907200*pp**103 + 451445491199/453600*pp**102 + 1195809624377/907200*pp**101 + 358919891903/226800*pp**100 + 542544299147/302400*pp**99 + 253801021099/129600*pp**98 + 1887257630221/907200*pp**97 + 49099889339/22680*pp**96 + 1005523910093/453600*pp**95 + 50807985899/22680*pp**94 + 1015738666219/453600*pp**93 + 502962466183/226800*pp**92 + 131763981613/60480*pp**91 + 482048043083/226800*pp**90 + 934807252927/453600*pp**89 + 257572297643/129600*pp**88 + 30899532707/16200*pp**87 + 551133092971/302400*pp**86 + 393398071727/226800*pp**85 + 186529850387/113400*pp**84 + 31343136029/20160*pp**83 + 13291526851/9072*pp**82 + 8921713159/6480*pp**81 + 3658252148/2835*pp**80 + 8106794459/6720*pp**79 + 14581492889/12960*pp**78 + 31659423493/30240*pp**77 + 1399648351/1440*pp**76 + 8167133419/9072*pp**75 + 10060890125/12096*pp**74 + 27809183167/36288*pp**73 + 63863354419/90720*pp**72 + 4176312551/6480*pp**71 + 7617266503/12960*pp**70 + 96813224677/181440*pp**69 + 9713510171/20160*pp**68 + 871683805/2016*pp**67 + 3883322333/10080*pp**66 + 381243057/1120*pp**65 + 428912629/1440*pp**64 + 2597163473/10080*pp**63 + 276996709/1260*pp**62 + 1859943523/10080*pp**61 + 191233549/1260*pp**60 + 306631363/2520*pp**59 + 29694269/315*pp**58 + 350393479/5040*pp**57 + 5314123/112*pp**56 + 94063609/3360*pp**55 + 111833017/10080*pp**54 - 3753171/1120*pp**53 - 26028389/1680*pp**52 - 256689301/10080*pp**51 - 28068427/840*pp**50 - 66356233/1680*pp**49 - 49123197/1120*pp**48 - 373553/8*pp**47 - 6745113/140*pp**46 - 11633611/240*pp**45 - 80207641/1680*pp**44 - 77507651/1680*pp**43 - 4908805/112*pp**42 - 9838801/240*pp**41 - 4231249/112*pp**40 - 549315/16*pp**39 - 103357459/3360*pp**38 - 15211811/560*pp**37 - 19869533/840*pp**36 - 710827/35*pp**35 - 9627103/560*pp**34 - 2292101/160*pp**33 - 2460523/210*pp**32 - 562981/60*pp**31 - 292843/40*pp**30 - 221269/40*pp**29 - 963017/240*pp**28 - 54597/20*pp**27 - 66403/40*pp**26 - 18893/24*pp**25 - 801/8*pp**24 + 19519/48*pp**23 + 22769/30*pp**22 + 14713/15*pp**21 + 32809/30*pp**20 + 135031/120*pp**19 + 16303/15*pp**18 + 118973/120*pp**17 + 10345/12*pp**16 + 86153/120*pp**15 + 23093/40*pp**14 + 53639/120*pp**13 + 19787/60*pp**12 + 2771/12*pp**11 + 1783/12*pp**10 + 257/3*pp**9 + 179/4*pp**8 + 59/3*pp**7 + 29/6*pp**6 - 23/6*pp**5 - 95/12*pp**4 - 25/3*pp**3 - 7*pp**2 - 4*pp - 1)/(pp**462 + 10*pp**461 + 53*pp**460 + 201*pp**459 + 616*pp**458 + 1626*pp**457 + 3841*pp**456 + 8325*pp**455 + 16841*pp**454 + 32186*pp**453 + 58631*pp**452 + 102482*pp**451 + 172779*pp**450 + 282148*pp**449 + 447819*pp**448 + 692818*pp**447 + 1047336*pp**446 + 1550276*pp**445 + 2250977*pp**444 + 3211112*pp**443 + 4506750*pp**442 + 6230563*pp**441 + 8494155*pp**440 + 11430486*pp**439 + 15196361*pp**438 + 19974951*pp**437 + 25978305*pp**436 + 33449806*pp**435 + 42666522*pp**434 + 53941406*pp**433 + 67625306*pp**432 + 84108746*pp**431 + 103823439*pp**430 + 127243498*pp**429 + 154886316*pp**428 + 187313097*pp**427 + 225129029*pp**426 + 268983093*pp**425 + 319567505*pp**424 + 377616790*pp**423 + 443906496*pp**422 + 519251565*pp**421 + 604504380*pp**420 + 700552510*pp**419 + 808316175*pp**418 + 928745455*pp**417 + 1062817273*pp**416 + 1211532184*pp**415 + 1375911002*pp**414 + 1556991293*pp**413 + 1755823759*pp**412 + 1973468540*pp**411 + 2210991460*pp**410 + 2469460241*pp**409 + 2749940706*pp**408 + 3053492988*pp**407 + 3381167763*pp**406 + 3734002526*pp**405 + 4113017929*pp**404 + 4519214199*pp**403 + 4953567649*pp**402 + 5417027295*pp**401 + 5910511594*pp**400 + 6434905318*pp**399 + 6991056579*pp**398 + 7579774013*pp**397 + 8201824128*pp**396 + 8857928823*pp**395 + 9548763084*pp**394 + 10274952866*pp**393 + 11037073166*pp**392 + 11835646285*pp**391 + 12671140277*pp**390 + 13543967582*pp**389 + 14454483844*pp**388 + 15402986915*pp**387 + 16389716039*pp**386 + 17414851208*pp**385 + 18478512678*pp**384 + 19580760635*pp**383 + 20721595008*pp**382 + 21900955423*pp**381 + 23118721289*pp**380 + 24374712003*pp**379 + 25668687257*pp**378 + 27000347436*pp**377 + 28369334099*pp**376 + 29775230535*pp**375 + 31217562384*pp**374 + 32695798305*pp**373 + 34209350675*pp**372 + 35757576309*pp**371 + 37339777195*pp**370 + 38955201243*pp**369 + 40603043042*pp**368 + 42282444617*pp**367 + 43992496183*pp**366 + 45732236899*pp**365 + 47500655636*pp**364 + 49296691774*pp**363 + 51119236040*pp**362 + 52967131402*pp**361 + 54839174037*pp**360 + 56734114401*pp**359 + 58650658434*pp**358 + 60587468928*pp**357 + 62543167081*pp**356 + 64516334252*pp**355 + 66505513931*pp**354 + 68509213937*pp**353 + 70525908845*pp**352 + 72554042632*pp**351 + 74592031517*pp**350 + 76638266960*pp**349 + 78691118786*pp**348 + 80748938393*pp**347 + 82810061996*pp**346 + 84872813852*pp**345 + 86935509406*pp**344 + 88996458307*pp**343 + 91053967247*pp**342 + 93106342578*pp**341 + 95151892665*pp**340 + 97188929931*pp**339 + 99215772564*pp**338 + 101230745874*pp**337 + 103232183298*pp**336 + 105218427061*pp**335 + 107187828505*pp**334 + 109138748111*pp**333 + 111069555260*pp**332 + 112978627793*pp**331 + 114864351441*pp**330 + 116725119192*pp**329 + 118559330654*pp**328 + 120365391480*pp**327 + 122141712925*pp**326 + 123886711603*pp**325 + 125598809501*pp**324 + 127276434286*pp**323 + 128918019929*pp**322 + 130522007664*pp**321 + 132086847300*pp**320 + 133610998901*pp**319 + 135092934829*pp**318 + 136531142130*pp**317 + 137924125236*pp**316 + 139270408955*pp**315 + 140568541726*pp**314 + 141817099109*pp**313 + 143014687470*pp**312 + 144159947813*pp**311 + 145251559709*pp**310 + 146288245284*pp**309 + 147268773233*pp**308 + 148191962825*pp**307 + 149056687862*pp**306 + 149861880551*pp**305 + 150606535255*pp**304 + 151289712097*pp**303 + 151910540393*pp**302 + 152468221892*pp**301 + 152962033794*pp**300 + 153391331516*pp**299 + 153755551185*pp**298 + 154054211839*pp**297 + 154286917322*pp**296 + 154453357859*pp**295 + 154553311293*pp**294 + 154586643974*pp**293 + 154553311293*pp**292 + 154453357859*pp**291 + 154286917322*pp**290 + 154054211839*pp**289 + 153755551185*pp**288 + 153391331516*pp**287 + 152962033794*pp**286 + 152468221892*pp**285 + 151910540393*pp**284 + 151289712097*pp**283 + 150606535255*pp**282 + 149861880551*pp**281 + 149056687862*pp**280 + 148191962825*pp**279 + 147268773233*pp**278 + 146288245284*pp**277 + 145251559709*pp**276 + 144159947813*pp**275 + 143014687470*pp**274 + 141817099109*pp**273 + 140568541726*pp**272 + 139270408955*pp**271 + 137924125236*pp**270 + 136531142130*pp**269 + 135092934829*pp**268 + 133610998901*pp**267 + 132086847300*pp**266 + 130522007664*pp**265 + 128918019929*pp**264 + 127276434286*pp**263 + 125598809501*pp**262 + 123886711603*pp**261 + 122141712925*pp**260 + 120365391480*pp**259 + 118559330654*pp**258 + 116725119192*pp**257 + 114864351441*pp**256 + 112978627793*pp**255 + 111069555260*pp**254 + 109138748111*pp**253 + 107187828505*pp**252 + 105218427061*pp**251 + 103232183298*pp**250 + 101230745874*pp**249 + 99215772564*pp**248 + 97188929931*pp**247 + 95151892665*pp**246 + 93106342578*pp**245 + 91053967247*pp**244 + 88996458307*pp**243 + 86935509406*pp**242 + 84872813852*pp**241 + 82810061996*pp**240 + 80748938393*pp**239 + 78691118786*pp**238 + 76638266960*pp**237 + 74592031517*pp**236 + 72554042632*pp**235 + 70525908845*pp**234 + 68509213937*pp**233 + 66505513931*pp**232 + 64516334252*pp**231 + 62543167081*pp**230 + 60587468928*pp**229 + 58650658434*pp**228 + 56734114401*pp**227 + 54839174037*pp**226 + 52967131402*pp**225 + 51119236040*pp**224 + 49296691774*pp**223 + 47500655636*pp**222 + 45732236899*pp**221 + 43992496183*pp**220 + 42282444617*pp**219 + 40603043042*pp**218 + 38955201243*pp**217 + 37339777195*pp**216 + 35757576309*pp**215 + 34209350675*pp**214 + 32695798305*pp**213 + 31217562384*pp**212 + 29775230535*pp**211 + 28369334099*pp**210 + 27000347436*pp**209 + 25668687257*pp**208 + 24374712003*pp**207 + 23118721289*pp**206 + 21900955423*pp**205 + 20721595008*pp**204 + 19580760635*pp**203 + 18478512678*pp**202 + 17414851208*pp**201 + 16389716039*pp**200 + 15402986915*pp**199 + 14454483844*pp**198 + 13543967582*pp**197 + 12671140277*pp**196 + 11835646285*pp**195 + 11037073166*pp**194 + 10274952866*pp**193 + 9548763084*pp**192 + 8857928823*pp**191 + 8201824128*pp**190 + 7579774013*pp**189 + 6991056579*pp**188 + 6434905318*pp**187 + 5910511594*pp**186 + 5417027295*pp**185 + 4953567649*pp**184 + 4519214199*pp**183 + 4113017929*pp**182 + 3734002526*pp**181 + 3381167763*pp**180 + 3053492988*pp**179 + 2749940706*pp**178 + 2469460241*pp**177 + 2210991460*pp**176 + 1973468540*pp**175 + 1755823759*pp**174 + 1556991293*pp**173 + 1375911002*pp**172 + 1211532184*pp**171 + 1062817273*pp**170 + 928745455*pp**169 + 808316175*pp**168 + 700552510*pp**167 + 604504380*pp**166 + 519251565*pp**165 + 443906496*pp**164 + 377616790*pp**163 + 319567505*pp**162 + 268983093*pp**161 + 225129029*pp**160 + 187313097*pp**159 + 154886316*pp**158 + 127243498*pp**157 + 103823439*pp**156 + 84108746*pp**155 + 67625306*pp**154 + 53941406*pp**153 + 42666522*pp**152 + 33449806*pp**151 + 25978305*pp**150 + 19974951*pp**149 + 15196361*pp**148 + 11430486*pp**147 + 8494155*pp**146 + 6230563*pp**145 + 4506750*pp**144 + 3211112*pp**143 + 2250977*pp**142 + 1550276*pp**141 + 1047336*pp**140 + 692818*pp**139 + 447819*pp**138 + 282148*pp**137 + 172779*pp**136 + 102482*pp**135 + 58631*pp**134 + 32186*pp**133 + 16841*pp**132 + 8325*pp**131 + 3841*pp**130 + 1626*pp**129 + 616*pp**128 + 201*pp**127 + 53*pp**126 + 10*pp**125 + pp**124),
                  2: 6470609940233185159138945357612238245604321432648268329298472229233744485577689689257395621446293689698402567383416151179175715467195461644076562143244259406127416262216856477974401024521802336370363808338767123337/6909618677543010824934020539571531692318398488001507419818595974007977478498753157497529034132135493698369286090266091593204503388812791614538788553909835258970193100389610648691267452562954039946804022843801600000,
                  3: 5837698007089661491967732407952987712831588458981657951760350646811606226700125271997223981166331505212174970806578007132637645831261098537390391801501923407761413844391307024604794702569496602398567551242517486661260260806669041002834796575549096134166055922354382451115045270730562331/6011523775695107675000522684690529143785496951103634781616937637021253758235219387695585649215332191157427051037095819626205020406879338940368869956527588898017206584804156474091421763557238839825934529908401938687029814895805668970540919215270714743761773596621130609559027882393600000,
                  5: 651829272410684487657987775390451297056565226774341657018756236394358211586177116540948489667227556299628081386626744190122136917837791080915248438896602790594916285703832458788864199680486959097359957212147639138160208601210677596651887467156257694253597217255904339913887523458301915846364736722366050940969949115309739834445953664662982011990471054372875434824853944055614568553988267804563627305553248357107/656134725324794386784435793197663390888555661090945160055011576856570159450237224618285363906004513251998156542833109253331148203467531078094707379124139183272606892716936167518944710782076280628961013576595360409273618848236161566243681136279081272632349256179888052380508054163417445393694289110126955490850994137300926686784612033896942303395914289170214733770691850622824858874082565307617187500000000000000,
                  7: 4512604870787864022848143904134314933484582973415773380844817869178198122035612375092466816851496022154453366689161634129463187082345137846970360981502360947482913404293240959655326943998516861852881781426363883920660481560837098849356475270009975548780126148520918141834495362809720647635472283815021465907035281949313938291444340620632029042276813058543216578721329790623191451443207496716422207283/4519712543036923006076136778356169199400166251968163477283090614088837431477577329518439461279032525567694687524877216848568014113236730355594579942649207241958588253446141139015731685991449369477423657851039805297393038814709940042480806274631840532741653291426469871748262309067311156898724125738857829456098791328072082458420589860177132594593846590700970735253115416241990022099337583001600000000}
}

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
#     points but not of the form u*h**2.  Includes scalings (the
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
#     such that z**2+h*z+f has no smooth points and either factors over
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
    u, with no smooth points but not of the form u*h**2, with
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

