Qp = FunctionField(QQ,'p')
pp = Qp.gen()


# Initialize dicts to store the Gamma_plus/minus sets but do not reset
#  on reload.  The dicts will be initialized if they don't exist
#  (e.g. on first loading the file) or have no entries.
#  Initialization of the dicts is done by the initialize_dicts()
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

def initialize_all_dicts():
    initialize_alpha_beta_dicts()
    initialize_Gamma_dicts()
    initialize_Delta_dicts()

def show_dicts():
    print("alpha_0:     {}".format(alpha_0_dict))
    print("alpha_plus:  {}".format(alpha_plus_dict))
    print("alpha_minus: {}".format(alpha_minus_dict))
    print("beta_0:      {}".format(beta_0_dict))
    print("beta_plus:   {}".format(beta_plus_dict))
    print("beta_minus:  {}".format(beta_minus_dict))

def N(j, p=pp):
    return sum([moebius(d)*p**(j//d) for d in divisors(j)]) / j

def Ndash(j, p=pp):
    return p+1 if j==1 else N(j)

def Phi(d, base=[1,1]):
    #print("Starting d={} with base ({},{})".format(d,base[0],base[1]))
    if d==0:
       yield []
    d0, e0 = base
    for di in [d0..d]:
    	e1 = e0 if di==d0 else 1
	for ei in [e1..d//di]:
	    #print("d={}, using (di,ei)=({},{})".format(d,di,ei))
	    for phi in Phi(d-di*ei,[di,ei]):
	        yield [[di,ei]] + phi

def deg_fp(phi):
    return sum([d*e for d,e in phi])

def m2(phi, jk):
    return len([de for de in phi if de==jk])

def m1(phi, j):
    return len([de for de in phi if de[0]==j])

def lambda_A(phi, p=pp):
    d = deg_fp(phi)
    return prod([prod([N(j,p)-i for i in srange(m1(phi,j))])/prod([factorial(m2(phi,[j,i])) for i in [1..j]]) for j in [1..d]]) / p**d

def lambda_P(phi, p=pp):
    d = deg_fp(phi)
    return prod([prod([Ndash(j,p)-i for i in srange(m1(phi,j))])/prod([factorial(m2(phi,[j,i])) for i in [1..j]]) for j in [1..d]]) / p**d

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
        Gamma_plus_dict[(q,d)] = [f for f in monics(F,d) if no_smooth_points(f)]
    return Gamma_plus_dict[(q,d)]

def Gamma_minus(d, F=None):
    if F==None:
       return []
    q = F.cardinality()
    if not (q,d) in Gamma_minus_dict:
        u = a_nonsquare(F)
        Gamma_minus_dict[(q,d)] = [f for f in monics(F,d,u) if not (u*f).is_square() and no_smooth_points(f)]
    return Gamma_minus_dict[(q,d)]

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
    return [homog(R(list(v))) for v in ProjectiveSpace(F,d)]

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

def Delta(F,d):
    q = F.cardinality()
    if not (q,d) in Delta_dict:
        u = a_nonsquare(F)
        flist = homog(F,d) # up to scaling
        # consider both f and u*f
        D1 =  [f for f in flist if not is_square_homog(u*f) and no_smooth_points_homog(f)]
        D2 =  [u*f for f in flist if not is_square_homog(f) and no_smooth_points_homog(u*f)]
        # D1+D2 is result up to scaling by squares
        sq = [F(a)^2 for a in [1..(q-1)//2]]
        Delta_dict[(q,d)] = flatten([[a*f for f in D1+D2] for a in sq])
    return Delta_dict[(q,d)]

def R(j,f):
    # set of roots of f of multiplicity j
    return [a for a,e in f.roots() if e==j]

def r(j,f):
    return len(R(j,f))

def Rplus(j,f):
    if j%2==1:
       return R(j,f)
    x = f.parent().gen()
    return [a for a in R(j,f) if (f//(x-a)**j)(a).is_square()]

def rplus(j,f):
    return len(Rplus(j,f))

def Rminus(j,f):
    if j%2==1:
        return []
    x = f.parent().gen()
    return [a for a in R(j,f) if not (f//(x-a)**j)(a).is_square()]

def rminus(j,f):
    return len(Rminus(j,f))

def affine(L,p):
    if len(L)==1:
        return L[0]
    return ((p-1)*L[0]+affine(L[1:],p))/p

def beta_0_helper(i, p=pp,v=None):
    # used in beta_i^0
    b= sum([lambda_A(phi,p) * prod([(1-alpha_0(e,p))
     for e in [1..i] if [1,e] in phi])
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
    F = GF(p) if p in ZZ else None
    return sum([lambda_A(phi,p) * prod([(1-alpha_minus(2*e,p,v))
     for e in [1..i] if [1,e] in phi])
      for phi in Phi(i)])

def beta_minus_helper_2(i,p=pp,v=None):
    # used in beta_2i^-
    F = GF(p) if p in ZZ else None
    return sum([prod([prod([1 if rpm(j,f)==0 else (1-alpha_eps(j,p,v))**len(rpm(j,f))
     for alpha_eps,rpm in zip([alpha_plus,alpha_minus],[rplus,rminus])])
      for j in [1..2*i]])
       for f in Gamma_minus(2*i,F)])

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
    v0 = "bp{}{}".format(i,p)
    if v==None:
        v=v0
        print("Setting "+v0)
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (i)
    print("Computing beta_plus({},{})".format(i,p))
    beta_plus_dict[(i,p)] = 1 - beta_plus_helper(i,p,v)/p^i
    return beta_plus_dict[(i,p)]

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
    v0 = "bm{}{}".format(i,p)
    if v==None:
        v=v0
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
            return PolynomialRing(F,v0).gen()
    # now i is even, use Prop 3.3(ii)
    print("Computing beta_minus({},{})".format(i,p))
    i2 = i//2
    beta_minus_dict[(i,p)] = 1 - beta_minus_helper_1(i2,p,v) / p^i2 - beta_minus_helper_2(i2,p,v) / p^i
    return beta_minus_dict[(i,p)]

def beta_0(i,p=pp,v=None):
    try:
        return beta_0_dict[(i,p)]
    except KeyError:
        if i<3:
            b =  beta_0_dict[(i,p)] = [0,1,1/2][i]
            return b
        pass
    v0 = "b0{}{}".format(i,p)
    if v==None:
        v=v0
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
            return PolynomialRing(F,v0).gen()
    # use Prop 3.3 (iii)
    print("Computing beta_0({},{})".format(i,p))
    beta_0_dict[(i,p)] = 1 - beta_0_helper(i,p,v)
    return beta_0_dict[(i,p)]

def alpha_0(i,p=pp,v=None):
    # NB circularity:  alpha_0(i) depends on beta_0(i) for i even and beta(i) for i odd!
    try:
        return alpha_0_dict[(i,p)]
    except KeyError:
        if i<3:
            a = alpha_0_dict[(i,p)] = [0,1,1/2][i]
            return a
    v0 = "a0{}{}".format(i,p)
    if v==None:
        v=v0
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
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
    alpha_0_dict[(i,p)] = affine(blist,p)
    return alpha_0_dict[(i,p)]

def alpha_plus(i,p=pp,v=None):
    try:
        return alpha_plus_dict[(i,p)]
    except KeyError:
        if i<3:
            a = alpha_0_dict[(i,p)] = [1,1,1/p][i]
            return a
    v0 = "ap{}{}".format(i,p)
    if v==None:
        v=v0
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
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
    alpha_0_dict[(i,p)] = affine(blist,p)
    return alpha_0_dict[(i,p)]

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
    v0 = "am{}{}".format(i,p)
    if v==None:
        v=v0
    else:
        if v==v0:
            print("recursion for "+v0)
            F = Qp if p==pp else QQ
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
    alpha_0_dict[(i,p)] = affine(blist,p)
    return alpha_0_dict[(i,p)]
