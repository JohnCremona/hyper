# Code for densities of splitting of binary forms over Q_p

from sage.all import prod
from basics import pp
from fact_pat import (lambda_A, lambda_P, split_factorizations)

# Initialize dicts to store the alphas and betas but do not reset on reload!
# The alpha and beta values for subscripts 0,1 are known directly.

def initialize_alpha_s_beta_s_dicts():
    global alpha_s_dict, beta_s_dict
    print("Initializing alpha_s_i for i=0,1 to 1")
    alpha_s_dict = {0:1, 1:1}
    print("Initializing beta_s_i for i=0,1 to 1")
    beta_s_dict =     {0:1, 1:1}

try:
    n = len(alpha_s_dict)
    n = len(beta_s_dict)
except NameError:
    alpha_s_dict = {}
    beta_s_dict = {}
    initialize_alpha_s_beta_s_dicts()

def show1dict(d,dn):
    print(dn+":")
    for k in sorted(d.keys()):
        print("\t(i,p)={}: {}".format(k,d[k]))

def show_alpha_s_dicts():
    show1dict(alpha_s_dict, "alpha_s")

def show_beta_s_dicts():
    show1dict(beta_s_dict, "beta_s")

def show_dicts():
    show_alpha_s_dicts()
    show_beta_s_dicts()

def make_alpha_s_beta_s(d):
    if d<2 or d in alpha_s_dict:
        return

    make_alpha_s_beta_s(d-1)

    h = sum( lambda_A(phi)*prod([alpha_s(e) for i,e in phi if e<d])
                 for phi in split_factorizations(d) if not [1,d] in phi)
    r = pp^(-d*(d-1)//2)
    s = pp^(-(d-1))
    beta_s_dict[d] = b = h/(1-r*s)
    alpha_s_dict[d] = r*b

def beta_s(i):
    """beta_s_i(p).

    Computed values are stored in beta_s_dict keyed on i.  If not yet
    computed, make_alpha_s_beta_s() computes both alpha_s(i) and beta_s(i),
    using recursion if necessary.
    """
    if not i in beta_s_dict:
        make_alpha_s_beta_s(i)
    return beta_s_dict[i]

def alpha_s(i):
    """ alpha_s_i(p).

    Computed values are stored in alpha_s_dict keyed on i.  If not yet
    computed, make_alpha_s_beta_s() computes both alpha_s(i) and beta_s(i),
    using recursion if necessary.
    """
    if not i in alpha_s_dict:
        make_alpha_s_beta_s(i)
    return alpha_s_dict[i]

# the overall probability

def rhostar(d):
    return sum( lambda_P(phi) * prod([alpha_s(e) for i,e in phi])
                for phi in split_factorizations(d)   )
