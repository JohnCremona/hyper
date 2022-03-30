# Code for densities of numbers of roots of binary forms over Q_p
#
# Use results of prob_roots.tex (MB, JEC, TAF, SG) to successively
# solve for alpha(n,d), beta(n,d), rho(n,d) and also alpha_star(n,d),
# etc.  Here n>=1 and 0<=d<=n.
#
# Here rho_star(n,d) is the density of polynomials of degree d over
# Z_p which have d roots in P^1(Q_p), while rho(n,d) is the expected
# number of subsets of d roots.  e.g. rho(n,1) is the expected number
# of roots, which is 1 for all n>0 (a result of Caruso).
#
# alpha_star(n,d) and alpha(n,d) are the same for monic polynomials of
# degree n.
#
# beta_star(n,d) and beta(n,d) are the same for monic polynomials of
# degree n which reduce to x^n mod p.
#
# rho(n,0) = alpha(n,0) = beta(n,0) = 1 for all n>=1.
#

from sage.all import (prod, binomial)

# pp is a generator of the rational function field Q(p)
# star is the operator which substitutes 1/p for p in a rational function

from basics import (pp, star, partitions)

# Phi(n) is a list of factorization patterns of degree n, denoted S(n) in the paper
# number_of_monics_with_splitting_type(sigma) is denoted N_sigma in the paper

from fact_pat import (number_of_monics_with_splitting_type, Phi)

debug = False #True

# Initialize dicts to store the alphas and betas but do not reset on reload!

try:
    n = len(alpha_dict)
except NameError:
    alpha_dict = {}

def initialize_alpha_dict():
    global alpha_dict
    alpha_dict = {}

try:
    n = len(beta_dict)
except NameError:
    beta_dict = {}

def initialize_beta_dict():
    global beta_dict
    beta_dict = {}

def initialize_alpha_beta_dicts():
    initialize_alpha_dict()
    initialize_beta_dict()

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t((n,d),p)={}: {}".format(k,d[k]))

def show_alpha_dict():
    show1dict(alpha_dict, "alpha")

def show_beta_dict():
    show1dict(beta_dict, "beta")

def show_dicts():
    show_alpha_dict()
    show_beta_dict()

def alpha_sigma(n,d,sigma):
    nis = [ei for di,ei in sigma if di==1]
    k = len(nis)
    if debug:
        print("In alpha_sigma() with (n,d)=({},{}) and sigma={}".format(n,d,sigma))
        print("--using beta(ni,di) for (ni,di) in {}".format([list(zip(nis,dis)) for dis in partitions(d,k)]))
    return sum([prod([beta(ni,di) for ni,di in zip(nis,dis)]) for dis in partitions(d,k)])

def make_alpha_beta(n, d, verbose=False):
    if debug:
        print("in make_alpha_beta(n,d) with n={}, d={}".format(n,d))
    if d<0 or d>n or n==1 or (n,d) in alpha_dict:
        if debug:
            print("nothing to do")
        return
    if debug:
        print("doing any necessary recursive calls...")
    # make values for smaller n, or same n and smaller d:
    for n1 in range(2,n):
        for d1 in range(1,n1+1):
            if debug:
                print("recursion for (n,d)=({},{})".format(n1,d1))
            make_alpha_beta(n1, d1, verbose)
    for d1 in range(1,d):
            if debug:
                print("recursion for (n,d)=({},{})".format(n,d1))
            make_alpha_beta(n, d1, verbose)

    if debug:
        print("... recursive calls done for (n,d)=({},{})".format(n,d))
    A = pp**(-n) * sum([alpha_sigma(n,d, sigma) * number_of_monics_with_splitting_type(sigma)
                       for sigma in Phi(n)
                       if sigma != [[1,n]] ])

    B = (pp-1) * sum([pp**(-binomial(r+1,2)) * sum([pp**s * alpha(s,d)
                                                   for s in range(r)])
                      for r in range(n)])

    D = 1 - pp**(1-binomial(n+1,2))
    assert D
    if debug:
        print("A = {}".format(A))
        print("B = {}".format(B))
        print("D = {}".format(D))

    a = (A+pp**(1-n)*B)/D
    b  = (pp**(-binomial(n,2))*A+B)/D
    if debug:
        print("(n,d)=({},{}): storing alpha={}, beta={}".format(n, d, a, b))
    alpha_dict[(n,d)] = a
    beta_dict[(n,d)]  = b

def beta(n,d):
    """beta(n,d;p).

    Computed values are stored in beta_dict keyed on (n,d).  If not
    yet computed, make_alpha_beta() computes and stores both
    alpha(n,d) and beta(n,d), using recursion if necessary.

    """
    if d<0 or d>n:
        return 0
    if d==0 or n==1:
        return 1
    if not (n,d) in beta_dict:
        make_alpha_beta(n,d)
    return beta_dict[(n,d)]

def alpha(n,d):
    """ alpha(n,d; p).

    Computed values are stored in alpha_dict keyed on (n,d).  If not
    yet computed, make_alpha_beta() computes and stores both
    alpha(n,d) and beta(n,d), using recursion if necessary.
    """
    if d<0 or d>n:
        return 0
    if d==0 or n==1:
        return 1
    if not (n,d) in beta_dict:
        make_alpha_beta(n,d)
    return alpha_dict[(n,d)]

def rho_m(n,d, m):
    return sum([alpha(m,d1)*beta(n-m,d-d1) for d1 in range(d+1)])

def rho(n,d):
    if d<0 or d>n:
        return 0
    if d==0 or n==1:
        return 1
    return ((pp-1)/(pp**(n+1)-1)) * sum([pp**m*rho_m(n,d, m) for m in range(n+1)])

def m1pow(k):
    return -1 if k%2 else 1

def alpha_star(n,r):
    return sum([m1pow(d-r)*binomial(d,r)*alpha(n,d) for d in range(n+1)])

def beta_star(n,r):
    return sum([m1pow(d-r)*binomial(d,r)*beta(n,d) for d in range(n+1)])

def rho_star(n,r):
    return sum([m1pow(d-r)*binomial(d,r)*rho(n,d) for d in range(n+1)])

# Three quantities defined in the paper

gamma = (pp**2+1)**2/(6*(pp**4+pp**3+pp**2+pp+1))
delta = (pp-1)**2/((pp**5-1)*(pp**9-1))
eta = 1/((pp+1)**2*(pp**4+pp**3+pp**2+pp+1))

nmax=6 # largest n for which we check general formulas

print("Checking that rho^*(n,n-1) = alpha^*(n,n-1) = beta^*(n,n-1) for n up to {}...".format(nmax), end="")
assert all([rho_star(n,n-1)==0 for n in range(1,nmax+1)])
assert all([alpha_star(n,n-1)==0 for n in range(1,nmax+1)])
assert all([beta_star(n,n-1)==0 for n in range(1,nmax+1)])
print("OK")

# check symmetry of rho(n,d) for 0 <= d <= n <= 5

print("Checking that rho(n,d) is invariant under p<-->1/p for n up to {}...".format(nmax), end="")
assert all([all([star(rho(n,d))==rho(n,d) for d in range(n+1)]) for n in range(1,nmax+1)])
print("OK")

# check symmetry between alpha(n,d) and beta(n,d) for 0 <= d <= n <= 5

print("Checking that alpha(n,d) and beta(n,d) are swapped by p<-->1/p for n up to {}...".format(nmax), end="")
assert all([all([star(alpha(n,d))==beta(n,d) for d in range(n+1)]) for n in range(1,nmax+1)])
print("OK")

# check special values from section 1.1.1

print("Checking values of alpha(n,1), beta(n,1), and rho(n,1) for n up to {}...".format(nmax), end="")
assert alpha(1,1)==1 and all([alpha(n,1)==pp/(pp+1) for n in range(2,nmax+1)])
assert beta(1,1)==1 and all([beta(n,1)==1/(pp+1) for n in range(2,nmax+1)])
assert all([rho(n,1)==1 for n in range(1,nmax+1)])
print("OK")

# check special values from section 1.1.2

print("Checking values of alpha(n,2), beta(n,2), and rho(n,2) for n up to {}...".format(nmax), end="")
assert 2*alpha(2,2)==pp/(pp+1) and 2*alpha(3,2)==eta*pp**3*(pp**3+1) and all([2*alpha(n,2)==eta*pp**3*(pp**3+pp+1) for n in range(4,nmax+1)])
assert 2*beta(2,2)==1/(pp+1) and 2*beta(3,2)==eta*(pp**3+1) and all([2*beta(n,2)==eta*(pp**3+pp**2+1) for n in range(4,nmax+1)])
assert 2*rho(2,2)==1 and all([2*rho(n,2)==(pp**2+1)**2/(pp**4+pp**3+pp**2+pp+1) for n in range(3,nmax+1)])
print("OK")

# check special values from section 1.1.3:

# rho*(2,r)

print("Checking values of rho^*(2,r)...", end="")
assert [2*rho_star(2,r) for r in range(3)] == [1, 0, 1]
print("OK")

# rho*(3,r)

print("Checking values of rho^*(3,r)...", end="")
assert [rho_star(3,r) for r in range(4)] == [2*gamma, 1-3*gamma, 0, gamma]
print("OK")

# rho*(4,r)

print("Checking values of rho^*(4,r)...", end="")
assert rho_star(4,0) == (delta/8) * (3*pp**12 + 5*pp**11 + 8*pp**10 +
                                     12*pp**9 + 13*pp**8 + 12*pp**7 +
                                     17*pp**6 + 12*pp**5 + 13*pp**4 +
                                     12*pp**3 + 8*pp**2 + 5*pp + 3)

assert rho_star(4,1) == (delta/3) * (pp**12 + 2*pp**11 + 4*pp**10 +
                                     3*pp**9 + 6*pp**8 + 7*pp**7 +
                                     2*pp**6 + 7*pp**5 + 6*pp**4 +
                                     3*pp**3 + 4*pp**2 + 2*pp + 1)

assert rho_star(4,2) == (delta/4) * (pp**12 + 3*pp**11 + 2*pp**10 +
                                     6*pp**9 + 5*pp**8 + 4*pp**7 +
                                     9*pp**6 + 4*pp**5 + 5*pp**4 +
                                     6*pp**3 + 2*pp**2 + 3*pp + 1)

assert rho_star(4,4) == (delta/24) * (pp**12 - pp**11 + 4*pp**10 +
                                      3*pp**8 + 4*pp**7 - pp**6 +
                                      4*pp**5 + 3*pp**4 + 4*pp**2 -pp
                                      + 1)
print("OK")

# alpha*(2,r)

print("Checking values of alpha^*(2,r)...", end="")
assert [alpha_star(2,r) for r in range(3)] == [(pp+2)/(2*(pp+1)), 0, pp/(2*(pp+1))]
print("OK")

# alpha*(3,r)

print("Checking values of alpha^*(3,r)...", end="")
assert 3*alpha_star(3,0) == (pp**4 + pp**3 + 3*pp**2 + 3)/(pp**4+pp**3+pp**2+pp+1)

assert 2*alpha_star(3,1) == (pp**5 + 3*pp**4 + pp**3 + 2*pp**2 + 2*pp)/((pp+1)*(pp**4+pp**3+pp**2+pp+1))

assert 6*alpha_star(3,3) == (pp**5 - pp**4 + pp**3)/((pp+1)*(pp**4+pp**3+pp**2+pp+1))
print("OK")

# alpha*(4,r)

print("Checking values of alpha^*(4,r)...", end="")
assert 8*alpha_star(4,0) == (3*pp**11 + 8*pp**10 + 6*pp**9 + 2*pp**8 -
                             3*pp**6 + 4*pp**5 - 4*pp**3 - 8*pp - 8)/((pp+1)**2 * (pp**9-1))

assert 3*alpha_star(4,1) == (pp**14 + 2*pp**12 - 6*pp**11 + 9*pp**10 -
                             9*pp**9 + 2*pp**8 + 3*pp**7 - 2*pp**6 - 3*pp**5 + 3*pp**4 - 3*pp**2 +
                             3*pp)/((pp**5-1) * (pp**9-1))

assert 4*alpha_star(4,2) == (pp**16 + 2*pp**15 - 4*pp**14 + 2*pp**13 +
                             2*pp**12 - 6*pp**11 + 4*pp**10 + 2*pp**9
                             - 6*pp**8 + 2*pp**7 + pp**6 - 2*pp**5 +
                             2*pp**3)/((pp+1)**2 * (pp**5-1) * (pp**9-1))

assert 24*alpha_star(4,4) == (pp**16 - 4*pp**15 + 6*pp**14 - 2*pp**13
                              - 4*pp**12 + 6*pp**11 - 4*pp**10 - 2*pp**9 + 6*pp**8 - 4*pp**7 +
                              pp**6)/((pp+1)**2 * (pp**5-1) * (pp**9-1))
print("OK")

