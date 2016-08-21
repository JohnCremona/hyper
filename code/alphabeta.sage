Qp = FunctionField(QQ,'p')
pp = Qp.gen()

def subs(f,p):
    n = f.numerator()(p)
    d = f.denominator()(p)
    if d:
        return n/d
    else:
        return sage.all.infinity

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

# Initialize dicts to store the alphas and betas but do not reset on reload!
try:
    n = len(alpha_0_dict)
except NameError:
    alpha_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(alpha_plus_dict)
except NameError:
    alpha_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1/pp}
try:
    n = len(alpha_minus_dict)
except NameError:
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

def initialize_alpha_dicts():
    global alpha_0_dict, alpha_plus_dict, alpha_minus_dict
    alpha_0_dict =      {(0,pp):0, (1,pp):1, (2,pp):1/2}
    alpha_plus_dict =   {(0,pp):1, (1,pp):1, (2,pp):1/pp}
    alpha_minus_dict =  {(0,pp):0, (1,pp):1, (2,pp):1/(pp+1)}

try:
    n = len(beta_0_dict)
except NameError:
    beta_0_dict = {(0,pp):0, (1,pp):1, (2,pp):1/2}
try:
    n = len(beta_plus_dict)
except NameError:
    beta_plus_dict = {(0,pp):1, (1,pp):1, (2,pp):1}
try:
    n = len(beta_minus_dict)
except NameError:
    beta_minus_dict = {(0,pp):0, (1,pp):1, (2,pp):pp/(pp+1)}

def initialize_beta_dicts():
    global beta_0_dict, beta_plus_dict, beta_minus_dict
    beta_0_dict =     {(0,pp):0, (1,pp):1, (2,pp):1/2}
    beta_plus_dict =  {(0,pp):1, (1,pp):1, (2,pp):1}
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

def show_dicts():
    print("alpha_0:     {}".format(alpha_0_dict))
    print("alpha_plus:  {}".format(alpha_plus_dict))
    print("alpha_minus: {}".format(alpha_minus_dict))
    print("beta_0:      {}".format(beta_0_dict))
    print("beta_plus:   {}".format(beta_plus_dict))
    print("beta_minus:  {}".format(beta_minus_dict))

def N(j, p=pp):
    if not (j,p) in N_dict:
        N_dict[(j,p)] = sum([moebius(d)*p**(j//d) for d in divisors(j)]) / j
    return N_dict[(j,p)]

def Ndash(j, p=pp):
    return p+1 if j==1 else N(j,p)

def Phi(d, base=[1,1]):
    if d==0:
       yield []
    d0, e0 = base
    for di in [d0..d]:
    	e1 = e0 if di==d0 else 1
	for ei in [e1..d//di]:
	    for phi in Phi(d-di*ei,[di,ei]):
	        yield [[di,ei]] + phi

def deg_fp(phi):
    return sum(d*e for d,e in phi)

def Phi1(d): # as for Phi(d) but only terms of the form [1,e]
    return [[de for de in phi if de[0]==1] for phi in Phi(d)]

def m2(phi, jk):
    return len([de for de in phi if de==jk])

def m1(phi, j):
    return len([de for de in phi if de[0]==j])

def lambda_helper(phi, NN, p=pp):
    d = deg_fp(phi)
    return prod([prod([NN(j,p)-i for i in srange(m1(phi,j))])/prod([factorial(m2(phi,[j,i])) for i in [1..d]]) for j in [1..d]])

def lambda_A(phi, p=pp):
    d = deg_fp(phi)
    return lambda_helper(phi, N, p) / p**d

def lambda_P(phi, p=pp):
    d = deg_fp(phi)
    return lambda_helper(phi, Ndash, p) * (p-1)/ (p**(d+1)-1)

def monics(F, d, u=1):
    Fx = PolynomialRing(F,'x')
    return [Fx(v.list()+[u]) for v in F^d]

def a_nonsquare(F):
    for u in F:
    	if not u.is_square():
	   return u
    raise ValueError

def no_smooth_points(f):
    # y^2=f(x) has no smooth F_p-points so for all x in F_p either
    # f(x) is nonsquare or it is 0 and x is a multiple root.
    fd = f.derivative()
    return all([(not f(x).is_square()) or (f(x)==fd(x)==0)
     for x in f.base_ring()])

def Gamma_plus(d,F=None):
    if F==None:
       return []
    q = F.cardinality()
    if not (q,d) in Gamma_plus_dict:
        print("Computing Gamma_plus({},{})".format(d,F))
        Gamma_plus_dict[(q,d)] = [f for f in monics(F,d) if no_smooth_points(f)]
    return Gamma_plus_dict[(q,d)]

def Gamma_minus(d, F=None):
    if F==None:
       return []
    q = F.cardinality()
    if not (q,d) in Gamma_minus_dict:
        print("Computing Gamma_minus({},{})".format(d,F))
        u = a_nonsquare(F)
        Gamma_minus_dict[(q,d)] = [f for f in monics(F,d,u) if not (u*f).is_square() and no_smooth_points(f)]
    return Gamma_minus_dict[(q,d)]

def show_Gamma(verbose=False):
    for d,dname in zip([Gamma_plus_dict, Gamma_minus_dict], ["Gamma^+","Gamma^-"]):
        print("\n{} entries".format(dname))
        for k in d.keys():
            if verbose:
                print("\t(p,d)={}: {}".format(k,d[k]))
            else:
                print("\t(p,d)={}: {} elements".format(k,len(d[k])))

def one_row(p):
    F = GF(p)
    return [len(ff) for ff in [Gamma_plus(1,F),
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

def homog(F, d):
    Fx = PolynomialRing(F,'x')
    Fxy = PolynomialRing(F,['x','y'])
    x, y = Fxy.gens()
    def homog(f):
    	return Fxy(y**d * f(x/y))
    return [homog(Fx(list(v))) for v in ProjectiveSpace(F,d)]

def is_square_homog(f):
    if f.degree()%2 ==1:
       return False
    F = f.base_ring()
    f_fac = f.factor()
    return F(f_fac.unit()).is_square() and all([e%2==0 for g,e in f_fac])

def no_smooth_points_homog(f):
    # z^2=f(x,y) has no smooth F_p-points so for all (x:y) in P^1(F_p) either
    # f(x,y) is nonsquare or it is 0 and (x:y) is a multiple root.
    x,y = f.parent().gens()
    fx = f.derivative(x)
    fy = f.derivative(y)
    P1 = ProjectiveSpace(f.base_ring(),1)
    return all([(not f(x,y).is_square()) or (fx(x,y)==fy(x,y)==f(x,y)==0)
     for x,y in P1])

def Delta(d,F=None):
    if F==None:
       return []
    q = F.cardinality()
    if not (q,d) in Delta_dict:
        print("Computing Delta({},{})".format(d,F))
        u = a_nonsquare(F)
        flist = homog(F,d) # up to scaling
        # consider both f and u*f
        D1 =  [f for f in flist if not is_square_homog(u*f) and no_smooth_points_homog(f)]
        D2 =  [u*f for f in flist if not is_square_homog(f) and no_smooth_points_homog(u*f)]
        # D1+D2 is result up to scaling by squares
        sq = [F(a)^2 for a in [1..(q-1)//2]]
        Delta_dict[(q,d)] = flatten([[a*f for f in D1+D2] for a in sq])
    return Delta_dict[(q,d)]

def show_Delta(verbose=False):
    for k in Delta_dict.keys():
        if verbose:
            print("(p,d)={}: {}".format(k,Delta_dict[k]))
        else:
            print("(p,d)={}: {} elements".format(k,len(Delta_dict[k])))


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
    if len(L)==1:
        return L[0]
    return ((p-1)*L[0]+affine(L[1:],p))/p

def beta_0_helper(i, p=pp,v=None):
    # used in beta_i^0
    b= sum([lambda_A(phi,p) *
            prod([(1-alpha_0(e,p,v)) for d,e in phi if d==1])
            for phi in Phi(i)])
    print("beta_0_helper({},{}) returns {}".format(i,p,b))
    return b

def beta_plus_helper(i,p=pp,v=None):
    # used in beta_i^+
    F = GF(p) if p in ZZ else None
    return sum([prod([prod([1 if rpm(j,f)==0 else (1-alpha_eps(j,p,v))**rpm(j,f)
     for alpha_eps,rpm in zip([alpha_plus,alpha_minus],[rplus,rminus])])
      for j in [1..i]])
       for f in Gamma_plus(i,F)])

def beta_minus_helper_1(i,p=pp,v=None):
    # used in beta_2i^-
    return sum([lambda_A(phi,p) *
                prod([(1-alpha_minus(2*e,p,v)) for d,e in phi if d==1])
                for phi in Phi(i)])

def beta_minus_helper_2(i,p=pp,v=None):
    # used in beta_i^- for even i
    F = GF(p) if p in ZZ else None
    return sum([prod([prod([1 if rpm(j,f)==0 else (1-alpha_eps(j,p,v))**rpm(j,f)
     for alpha_eps,rpm in zip([alpha_plus,alpha_minus],[rplus,rminus])])
      for j in [1..i]])
       for f in Gamma_minus(i,F)])

def beta(i,p=pp,v=None):
    return (beta_plus(i,p,v)+beta_minus(i,p,v))/2

def alpha(i,p=pp,v=None):
    return (alpha_plus(i,p,v)+alpha_minus(i,p,v))/2

def beta_plus(i,p=pp,v=None):
    try:
	return beta_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            b = beta_plus_dict[(i,p)] = 1
            return b
        pass
    F = Qp if p==pp else QQ
    v0 = "bp_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (i)
    print("Computing beta_plus({},{})".format(i,p))
    b = 1 - beta_plus_helper(i,p,v)/p^i
    try:
        b=F(b)
        beta_plus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("{}={}".format(v0,b))
            beta_plus_dict[(i,p)] = b
    return b

def beta_minus(i,p=pp,v=None):
    try:
        return beta_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            b = beta_minus_dict[(i,p)] = [0,1,p/(p+1)][i]
            return b
    if i%2==1:
       b = beta_minus_dict[(i,p)] = beta_plus(i,p,v)
       return b
    F = Qp if p==pp else QQ
    v0 = "bm_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # now i is even, use Prop 3.3(ii)
    print("Computing beta_minus({},{})".format(i,p))
    i2 = i//2
    b = 1 - beta_minus_helper_1(i2,p,v) / p^i2 - beta_minus_helper_2(i,p,v) / p^i
    try:
        b=F(b)
        beta_minus_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("{}={}".format(v0,b))
            beta_minus_dict[(i,p)] = b
    return b

def beta_0(i,p=pp,v=None):
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            b =  beta_0_dict[(i,p)] = [0,1,1/2][i]
            return b
    F = Qp if p==pp else QQ
    v0 = "b0_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (iii)
    print("Computing beta_0({},{})".format(i,p))
    b = 1 - beta_0_helper(i,p,v)
    try:
        b=F(b)
        beta_0_dict[(i,p)] = b
    except (ValueError, TypeError):
        # b is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,b))
        if str(b.parent().gen())==v0:
            r,s = b.list()
            b = r/(1-s)
            print("{}={}".format(v0,b))
            beta_0_dict[(i,p)] = b
    return b

def alpha_0(i,p=pp,v=None):
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            a = alpha_0_dict[(i,p)] = [0,1,1/2][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "a0_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_0({},{})".format(i,p))
    i2 = i//2 # so i=2*i2 or 2*i2+1
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
    if i%2==0:
       blist += [beta_0(i,p,v)]
    else:
       blist += [beta(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        alpha_0_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            alpha_0_dict[(i,p)] = a
    return a

def alpha_plus(i,p=pp,v=None):
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            a = alpha_0_dict[(i,p)] = [1,1,1/p][i]
            return a
    F = Qp if p==pp else QQ
    v0 = "ap_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_plus({},{})".format(i,p))
    i2 = i//2 # so i=2*i2 or 2*i2+1
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
    if i%2==0:
       blist += [beta_plus(i,p,v)]
    else:
       blist += [beta_0(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    print("{}={} (in {})".format(v0,a,a.parent()))
    try:
        a=F(a)
        alpha_plus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            alpha_plus_dict[(i,p)] = a
    return a

def alpha_minus(i,p=pp,v=None):
    try:
        return alpha_minus_dict[(i,p)]
    except KeyError:
        if i<3:
            a = alpha_0_dict[(i,p)] = [0,1,1/(p+1)][i]
            return a
    if i%2==1:
       alpha_minus_dict[(i,p)] = alpha_plus(i,p)
       return alpha_minus_dict[(i,p)]
    F = Qp if p==pp else QQ
    v0 = "am_{}_{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            return PolynomialRing(F,v0).gen()
    print("Computing alpha_minus({},{})".format(i,p))
    i2 = i//2 # so i=2*i2
    blist = []
    for j in [0..i2]:
      if j%2==0:
         blist += [beta_0(k,p,v) for k in [j,j-1..0]]
      else:
         blist += [beta(k,p,v) for k in [j,j-1..0]]
    blist += [beta_minus(i,p,v)]
    print("Computing affine({}) with p={}".format(blist,p))
    a = affine(blist,p)
    try:
        a=F(a)
        alpha_minus_dict[(i,p)] = a
    except (ValueError, TypeError):
        # a is a linear poly in some variable: is it v0?
        print("{}={}".format(v0,a))
        if str(a.parent().gen())==v0:
            r,s = a.list()
            a = r/(1-s)
            print("{}={}".format(v0,a))
            alpha_minus_dict[(i,p)] = a
    return a

# function for checking with Tom for suffixes i=3, 4

def check3():
    a = alpha_plus(3,3)
    if a==50246/177147:
        print("alpha_3^+(3) OK")
    else:
        print("alpha_3^+(3) = {} is WRONG".format(a))

    a = alpha_minus(3,3)
    if a==50246/177147:
        print("alpha_3^-(3) OK")
    else:
        print("alpha_3^-(3) = {} is WRONG".format(a))

    a = alpha_0(3,3)
    if a==431/729:
        print("alpha_3^0(3) OK")
    else:
        print("alpha_3^0(3) = {} is WRONG".format(a))

    a = alpha_plus(3)
    if a==(6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8):
        print("alpha_3^+(p) OK")
    else:
        print("alpha_3^+(p) = {} is WRONG".format(a))

    a = alpha_minus(3)
    if a==(6*pp**7-3*pp**6+pp**5-pp**3+3*pp**2-6*pp+6)/(6*pp**8):
        print("alpha_3^-(p) OK")
    else:
        print("alpha_3^-(p) = {} is WRONG".format(a))

    a = alpha_0(3)
    if a==(pp**3+pp**2-2*pp+2)/(2*pp**3):
        print("alpha_3^0(p) OK")
    else:
        print("alpha_3^0(p) = {} is WRONG".format(a))

def check4():
    a = alpha_plus(4,3)
    if a==16600/59049:
        print("alpha_4^+(3) OK")
    else:
        print("alpha_4^+(3) = {} is WRONG".format(a))

    a = alpha_plus(4,5)
    if a==352624/1953125:
        print("alpha_4^+(5) OK")
    else:
        print("alpha_4^+(5) = {} is WRONG".format(a))

    a = alpha_plus(4)
    if a==(pp**2+1)*(2*pp**3-pp**2-2*pp+2)/(2*pp**6):
        print("alpha_4^+(p) OK")
    else:
        print("alpha_4^+(p) = {} is WRONG".format(a))

    a = alpha_minus(4)
    if a==(2*pp**10+3*pp**9-p**5+2*pp**4-2*pp**2-3*pp-1)/(2*(pp+1)**2 *(p**9-1)):
        print("alpha_4^-(p) OK")
    else:
        print("alpha_4^-(p) = {} is WRONG".format(a))

    a = alpha_0(4)
    if a==(4*pp**10+8*pp**9-4*pp**8+4*pp**6-3*pp**4+pp**3-5*pp-5)/(8*(pp+1)*(p**9-1)):
        print("alpha_4^0(p) OK")
    else:
        print("alpha_4^0(p) = {} is WRONG".format(a))

# expressions in the formulas (Prop 3.5) linking mu_0 and mu_1 to each other.

def mu0_term_1(g,p=pp):
    d=g+1
    return sum([lambda_P(phi,p) * prod([(1-alpha_minus(2*e,p))
     for r,e in phi if r==1])
       for phi in Phi(d)])

def mu0_term_2(g,p=pp):
    F = GF(p) if p in ZZ else None
    d=2*g+2
    return sum([prod([prod([1 if rpm(j,f)==0 else (1-alpha_eps(j,p))**rpm(j,f)
     for alpha_eps,rpm in zip([alpha_plus,alpha_minus],[rplus,rminus])])
      for j in [1..d]])
       for f in Delta(d,F)])

def mu1_term(g,p=pp):
    d=2*g+2
    return sum([lambda_P(phi,p) * prod([(1-alpha_0(e,p))
     for r,e in phi if r==1])
       for phi in Phi(d)])

# if A = mu0_term_1
#    B = mu0_term_2
#    C = mu1_term
#
# then mu0 = (p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * (B + mu1)
# and  mu1 = (p^(2*g+3)-1)/(p^(2*g+3)) * C + 1/p^(2*g+3) * mu0
#
#
# so mu0 * (1-1/p^(4*g+6)) = (p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * B + (p^(2*g+3)-1)/(p^(4*g+6)) * C

def mu01(g,p=pp):
    A = mu0_term_1(g,p)
    B = mu0_term_2(g,p)
    C = mu1_term(g,p)
    ans0 =  ((p^(g+2)-1)/(2*p^(2*g+3)) * A + 1/p^(2*g+3) * B + (p^(2*g+3)-1)/(p^(4*g+6)) * C) / (1-1/p^(4*g+6))
    ans1 =  ((p^(2*g+3)-1) * C + ans0) / p^(2*g+3)
    assert ans0 == (p^(g+2)-1)/(2*p^(2*g+3)) * A +  (B + ans1) / p^(2*g+3)
    return ans0, ans1

def mu0(g,p=pp):
    return mu01(g,p)[0]

def mu1(g,p=pp):
    return mu01(g,p)[1]

def rho(g,p=pp):
    return 1 - mu0(g,p)

def check_rho(g,p=pp):
    if g==1:
        r = rho(1)
        rt = (8*p**10+8*p**9-4*p**8+2*p**6+p**5-2*p**4+p**3-p**2-8*p-5)/(8*(p+1)*(p**9-1))
        if r==rt:
            print("rho_1(p) OK")
        else:
            print("rho_1(p) = {} is WRONG, should be {}".format(r,rt))
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

