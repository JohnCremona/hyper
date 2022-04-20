# code from alphabetas.ipynb for testing

from basics import (pp, subs)
from sage.all import Set, primes
# Do this first:

#%runfile alphabeta.sage

# since this won't work from a .sage file:

# from alphabeta import (restore_Gammas, Gamma_plus_dict, Gamma_minus_dict, one_row,
#                        alpha_0_dict, alpha_plus_dict, alpha_minus_dict,
#                        beta_0_dict, beta_plus_dict, beta_minus_dict,
#                        initialize_alpha_beta_dicts, make_betas, rho,
#                        check_ab, check_rho)

restore_Gammas()


print("Gamma(n,1) precomputed for these primes and degree ranges:")

print([(p,Set([k[1] for k in Gamma_plus_dict.keys() if k[0]==p]))
         for p in Set([k[0] for k in Gamma_plus_dict.keys()])])

print("Gamma(n,u) precomputed for these primes and degree ranges:")

print([(p,Set([k[1] for k in Gamma_minus_dict.keys() if k[0]==p]))
         for p in Set([k[0] for k in Gamma_minus_dict.keys()])])

print()
print("*"*80)
print()
smallp = list(primes(3,32))
print("Check that the code for computing |Gamma(n,eps; p)| agrees with the table in the paper ( for odd p up to {}".format(max(smallp)))

for p in smallp:
    one_row(p)

# NB since we do not yet have Gamma(n,eps) for n>8, we
# will not obtain correct density formulas for g>=4 except at
# primes for which the additional Gamma(n,eps) are known to be empty.
# For n=0,1,2 we initialize the values alpha(n,eps) and beta(n,eps) for general p:

initialize_alpha_beta_dicts()

print("For n up to 10 we use the recursive formulas to compute all beta(n,eps)")

for i in range(3,11):
    print("i={}".format(i), end=", ")
    make_betas(i, verbose=False)

print("We now have the following beta(n,eps):")


for d in [beta_0_dict, beta_plus_dict, beta_minus_dict]:
    print(list(d.keys()))


print("and in the course of computing these we have also computed these alpha(n,eps):")

for d in [alpha_0_dict, alpha_plus_dict, alpha_minus_dict]:
    print(list(d.keys()))

print()
print("*"*80)
print()
smallp = [2,3,5,7,11,13]
print("For some small p (up to {}) we need to compute alpha(n,eps;p) and beta(n,eps; p) separately\n since the generic formulas are only valid for sufficiently large p:".format(max(smallp)))

for p in smallp:
    print("p={}".format(p))
    make_betas(8,p, verbose=False)

print("The stored alpha(n,eps) are now")

for d in [alpha_0_dict, alpha_plus_dict, alpha_minus_dict]:
    print(list(d.keys()))

print(" and the stored beta(n,eps) are:")

for d in [beta_0_dict, beta_plus_dict, beta_minus_dict]:
    print(list(d.keys()))

print()
print("*"*80)
print()
print("Check alpha and beta values:")
check_ab()

print("Check rho values:")
for g in [1,2]:
    check_rho(g)

print()
print("*"*80)
print()
print("Genus 1 densities: generic formula:")

rho1p = rho(1,pp)
print("{}\n =\n {}".format(rho1p,rho1p.factor()))

print("For the first few primes (p < 50) these are:")

for p in primes(50):
    r1p = rho(1,p)
    print("p={}: {} = {}".format(p,r1p,r1p*1.0))

print("The generic formula is valid all the way down to p=2:")

all([subs(rho1p,p)==rho(1,p) for p in primes(14)])

print()
print("*"*80)
print()
print("Genus 2 densities: generic formula")

rho2p = rho(2,pp)
print("{}\n =\n {}".format(rho2p,rho2p.factor()))

print("The first few values (p <= 17) computed individually:")

for p in primes(18):
    print("p={}: {} = {}".format(p,rho(2,p),rho(2,p)*1.0))

print("Of these, the generic formula is not valid for p<13:")

for p in primes(18):
    print("p={}: {}".format(p,"general formula valid" if rho(2,p)==subs(rho2p,p) else "special case"))

print()
print("*"*80)
print()
print("Genus 3 densities: generic formula:")

rho3p = rho(3,pp)
print("{}\n =\n {}".format(rho3p,rho3p.factor()))

print("The first few values (p<30) computed individually:")

for p in primes(30):
    print("p={}: {} = {}".format(p,rho(3,p),rho(3,p)*1.0))
for p in primes(3,30):
    print("p={} & {} \\\\".format(p,rho(3,p)))

print("Of these, the generic formula is not valid for p<29:")

for p in primes(30):
    print("p={}: {}".format(p,"general formula valid" if rho(3,p)==subs(rho3p,p) else "special case"))
