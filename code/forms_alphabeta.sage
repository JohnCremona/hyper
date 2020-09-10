# Code for densities of solubility for binary forms over Q_p

from sage.all import (prod, binomial)
from basics import (pp, affine)
from fact_pat import (lambda_A, lambda_P, Phi)

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

def initialize_all_dicts():
    initialize_alpha_beta_dicts()

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

def make_alpha_beta(d, verbose=False):
    if d<2 or d in alpha_dict:
        return

    make_alpha_beta(d-1, verbose)

    blist = sum([[beta(k) for k in range(j,-1,-1)] for j in range(d-1)], [])
    g = affine(blist,pp)
    h = 1 - sum( lambda_A(phi)*prod([1-alpha(e) for i,e in phi if i==1 and e<d])
                 for phi in Phi(d) )
    r = pp^(-d*(d-1)//2)
    s = pp^(-d+1)
    rs1 = 1-r*s
    alpha_dict[d] = (g+r*h)/rs1
    beta_dict[d] = (s*g+h)/rs1

def beta(i):
    """beta_i(p).

    Computed values are stored in beta_dict keyed on i.  If not yet
    computed, make_alpha_beta() computes both alpha(i) and beta(i),
    using recursion if necessary.
    """
    if not i in beta_dict:
        make_alpha_beta(i)
    return beta_dict[i]

def alpha(i):
    """ alpha_i(p).

    Computed values are stored in alpha_dict keyed on i.  If not yet
    computed, make_alpha_beta() computes both alpha(i) and beta(i),
    using recursion if necessary.
    """
    if not i in alpha_dict:
        make_alpha_beta(i)
    return alpha_dict[i]

# the overall probability

def rho(d):
    make_alpha_beta(d)
    mu = (pp-1) * sum(pp^i * (1-alpha(d-i))*(1-beta(i)) for i in range(d+1))
    return 1 - mu / (pp^(d+1) - 1)

def rho_new(d):
    make_alpha_beta(d)
    return 1 - sum(lambda_P(phi) * prod([1-alpha(e) for d,e in phi if d==1]) for phi in Phi(d))

def gamma(d):
    return alpha(d) - pp^-binomial(d,2)*beta(d)

def delta(d):
    return beta(d) - pp^(1-d)*alpha(d)

