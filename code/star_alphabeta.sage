# Code for densities of splitting of binary forms over Q_p

# Code for densities of solubility for binary forms over Q_p

from sage.all import prod
from basics import pp
from fact_pat import (lambda_A, lambda_P, split_factorizations)

# Initialize dicts to store the alphas and betas but do not reset on reload!
# The alpha and beta values for subscripts 0,1 are known directly.
try:
    n = len(alpha_dict)
    n = len(beta_dict)
except NameError:
    print("Initializing alpha_i for i=0,1 to 1")
    alpha_dict = {0:1, 1:1}
    print("Initializing beta_i for i=0,1 to 1")
    beta_dict = {0:1, 1:1}

def initialize_alpha_beta_dicts():
    global alpha_dict, beta_dict
    print("Initializing alpha_i for i=0,1 to 1")
    alpha_dict = {0:1, 1:1}
    print("Initializing beta_i for i=0,1 to 1")
    beta_dict =     {0:1, 1:1}

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

def make_alpha_beta(d):
    if d<2 or d in alpha_dict:
        return

    make_alpha_beta(d-1)

    h = sum( lambda_A(phi)*prod([alpha(e) for i,e in phi if e<d])
                 for phi in split_factorizations(d) if not [1,d] in phi)
    r = pp^(-d*(d-1)//2)
    s = pp^(-(d-1))
    beta_dict[d] = b = h/(1-r*s)
    alpha_dict[d] = r*b

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

def rhostar(d):
    return sum( lambda_P(phi) * prod([alpha(e) for i,e in phi])
                for phi in split_factorizations(d)   )
