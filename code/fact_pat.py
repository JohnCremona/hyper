# code for listing factorization patterns of forms and polynomials,
# with associated affine and projective density functions

from sage.all import (ZZ, moebius, prod, factorial)
from basics import pp

try:
    n = len(N_dict)
except NameError:
    N_dict = {}

def initialize_N_dict():
    global N_dict
    N_dict = {}

def N(j, p=pp):
    """The number of degree j monic irreducibles in GF(p)[X].
    """
    j = ZZ(j)
    if not j in N_dict:
        N_dict[j] = sum([moebius(d)*p**(j//d) for d in j.divisors()]) / j
    return N_dict[j]

def Ndash(j, p=pp):
    """The number of degree j homogeneous irreducibles in GF(p)[X,Y] up to scaling.
    """
    return p+1 if j==1 else N(j, p)

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
    return prod([prod([NN(j, p)-i for i in
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

def split_factorizations(d):
    """List of factorization patterns in degree d in which all factors are
    degree 1.
    """
    return [phi for phi in Phi(d) if all(d==1 for d,e in phi)]
