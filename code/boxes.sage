# Definition of discriminant and elated functions for quadratics,
# cubics and quartics:

def disc2(a,b,c):
    return b*b-4*a*c

def Disc2(abc):
    return disc2(*abc)

def disc3(a,b,c,d):
    return b^2*c^2 - 4*a*c^3 - 4*b^3*d + 18*a*b*c*d - 27*a^2*d^2

def Disc3(abcd):
    return disc3(*abcd)

def i4(a,b,c,d,e):
    return 12*a*e-3*b*d+c^2

def j4(a,b,c,d,e):
    return 72*a*c*e+9*b*c*d-27*a*d^2-27*e*b^2-2*c^3

def h4(a,b,c,d,e):
    return 8*a*c-3*b^2

def negh4(a,b,c,d,e):
    return 3*b^2-8*a*c

def q4(a,b,c,d,e):
    return 3*b^4 + 16*(a^2*(c^2+b*d)-a*b^2*c) - 64*a^3*e

def disc4(a,b,c,d,e):
    return 4*i4(a,b,c,d,e)^3-j4(a,b,c,d,e)^2

def Disc4(abcde):
    return disc4(*abcde)

def H4(abcde):
    return h4(*abcde)

def negH4(abcde):
    return negh4(*abcde)

def Q4(abcde):
    return q4(*abcde)

def base_box(d):
    return [RIF(-1,1) for _ in range(d)]

def vol(B): # allow cuboids!
    return prod([b.absolute_diameter() for b in B])

# General purpose recursive function to find the sub-volume of
# d-dimensional box B in which F>0, with tolerance vol, meaning that
# for sub-boxes of volume v<tol on which F is indefinite the interval
# [0,v] is returned instead of recursing.

def Fvol(B,F,tol,v=None):
    if not v:
        v = vol(B)  # the box's volume

    y = F(B)    # the value (range) of F on this box
    if y>=0:            # add v as F>=0 throughout
        return v
    if y<=0:            # add nothing as F<=0 throughout
        return 0
    if v < tol:         # add the range [0,v] if v is small
        return RIF(0,v)

    # Now subdivide the box into 2^d smaller boxes and recurse

    d = len(B)  # the dimension
    v2 = v/2**d
    C = [b.bisection() for b in B] # list of pairs
    return sum([Fvol([c[i] for i,c in zip(n.digits(base=2,padto=d),C)],F,tol,v2)
                for n in srange(2**d)])  # sum of 2^d sub-values

# Alternative versions of previous making use of homogeneity of F, so
# only the "outer shell" is considered explicitly.  First parameter d
# is the dimension (=number of variables in F)

def Fvold(d,F,tol,k=2):
    Ilist = [RIF(-1+i/k,-1+(i+1)/k) for i in range(2*k)]
    Blist = [t for t in cartesian_product_iterator([Ilist for _ in range(d)])]
    Blist = [b for b in Blist if not all([0 in x for x in b])]
    v = 1.0/k^d
    return sum([Fvol(b,F,tol,v) for b in Blist])*k^d/((2^d)*(k^d-1))

def quad_exact():
    var('a','b','c')
    assume(a>0)
    assume(b>0)
    assume(c>0)
    assume(a<1)
    assume(b<1)
    assume(c<1)
    r = integral(integral(integral(1,c,b^2/(4*a),1),a,b^2/4,1),b,0,1)
    r = r.simplify_exp()
    r = 1-r/2
    return r

def sampleDisc2(N):
    n=0
    for i in xrange(N):
        a = RDF.random_element(-1,1)
        b = RDF.random_element(-1,1)
        c = RDF.random_element(-1,1)
        if Disc2([a,b,c])>=0:
            n+=1
    return (1.0*n)/N

def quadratic_non_neg(N):
    print("exact value is (6*log(2)+113)/144 = %s" % ((6*log(2)+113)/144).n())
    return (1+sampleDisc2(N))/2

def sampleDisc3(N):
    n=0
    for i in xrange(N):
        a = RDF.random_element(-1,1)
        b = RDF.random_element(-1,1)
        c = RDF.random_element(-1,1)
        d = RDF.random_element(-1,1)
        if Disc3([a,b,c,d])>=0:
            n+=1
    return (1.0*n)/N

# r = quad_exact(); print r
# (6*log(2) + 41)/72
# print r.n()
# 0.627206709491107

def show(r):
    print("%s, diameter %s" %(r.endpoints(), r.absolute_diameter()))

def quad_interval(tol):
    r = Fvol3(F,tol,2)
    show(r)
    return r

# tol=10^-6 gives (0.623411996023995, 0.631484440394811) 0.00807244437081489

def cubic_interval(tol):
    r = Fvol4(Disc3,tol,2)
    show(r)
    return r

# Sample with 10^6 gives 0.218065
# Interval with tol=10^-4 gives (0.1442342, 0.3652547) diameter 0.2210205 (30s)
#               tol=10^-5 gives (0.1779510, 0.2965156) diameter 0.1185646 (4.5m)
#               tol=10^-6 gives (0.1779510, 0.2965156) diameter 0.1185646
#               tol 10^-7 gives (0.1963697, 0.2597123) diameter 0.0633425 (42m)

# QUARTICS
# 2 real roots if D<0
# 0 real roots if D>0 and (H>0 or Q<0)
# 4 real roots if D>0 and H<0 and Q>0

# Fs will be a vector of functions; we find the volume where all are positive, so we'll call this with [Disc4,negH4,Q4]

def FFvol(B,Fs,tol,v=None):
    if not v:
        v = vol(B)  # the box's volume

    all_pos = True
    for F in Fs:
        y = F(B)
        if y<=0:
            return 0
        if not y>=0:
            all_pos = False
    if all_pos:
        return v
    if v < tol:         # add the range [0,v] if v is small
        return RIF(0,v)

    # Now subdivide the box into 2^d smaller boxes and recurse

    d = len(B)  # the dimension
    v2 = v/2**d
    C = [b.bisection() for b in B] # list of pairs
    return sum([FFvol([c[i] for i,c in zip(n.digits(base=2,padto=d),C)],Fs,tol,v2)
                for n in srange(2**d)])  # sum of 2^d sub-values

# Version for quartics, returning 3 triple for the densities of 1, 2,
# 4 real roots:
#
# 2 real roots if D<0
# 0 real roots if D>0 and (H>0 or Q<0)
# 4 real roots if D>0 and H<0 and Q>0

R3 = RIF^3

def QuarticVol(B,tol,v=None):
    if not v:
        v = vol(B)  # the box's volume

    D = Disc4(B)
    if D<=0:
        return R3([0,v,0])
    if D>=0:
        H = H4(B)
        Q = Q4(B)
        if H>=0 or Q<=0:
            return R3([v,0,0])
        if H<=0 and Q>=0:
            return R3([0,0,v])

    if v < tol:         # add the range [0,v] if v is small
        return R3([RIF(0,v) for _ in range(3)])

    # Now subdivide the box into 2^d smaller boxes and recurse

    d = len(B)  # the dimension
    v2 = v/2**d
    C = [b.bisection() for b in B] # list of pairs
    return sum([QuarticVol([c[i] for i,c in zip(n.digits(base=2,padto=d),C)],tol,v2)
                for n in srange(2**d)])  # sum of 2^d sub-values

# Function which only returns the volume of the negative definite quartics
def QuarticNDVol(B,tol,v=None):
    if not v:
        v = vol(B)  # the box's volume

    if B[0]>=0 or B[4]>=0 or sum(B)>=0:
        return 0
    D = Disc4(B)
    if D<=0:   # 2 real roots
        return 0
    if D>=0:
        H = H4(B)
        Q = Q4(B)
        if H>=0 or Q<=0:  # 0 real roots
            return v      # We know that a<0 so not pos def!
        if H<=0 and Q>=0: # 4 real roots
            return 0

    if v < tol:         # add the range [0,v] if v is small
        return RIF(0,v)

    # Now subdivide the box into 2^d smaller boxes and recurse

    d = len(B)  # the dimension
    v2 = v/2**d
    C = [b.bisection() for b in B] # list of pairs
    return sum([QuarticNDVol([c[i] for i,c in zip(n.digits(base=2,padto=d),C)],tol,v2)
                for n in srange(2**d)])  # sum of 2^d sub-values


def QuarticNDVolShell(tol,k=2):
    d = 5
    Ilist = [RIF(-1+i/k,-1+(i+1)/k) for i in range(2*k)]
    Blist = [t for t in cartesian_product_iterator([Ilist for _ in range(d)])]
    Blist = [b for b in Blist if not all([0 in x for x in b])]
    v = 1.0/k^d
    return sum([QuarticNDVol(b,tol,v) for b in Blist])*k^d/(k^d-1)


# Version using the fact that being negative definite is a convex
# condition, so use intervals for the output but not for the boxes.
# Each box is now simply a 5-tuple of pairs.

def is_quartic_neg_def(abcde):
    a,b,c,d,e = abcde
    if a>=0 or e>=0 or a+b+c+d+e>=0 or a-b+c-d+e>=0:
        return False
    if disc4(a,b,c,d,e) <= 0:
        return False
    # now D>0, we require H>0 or Q<0
    return (h4(a,b,c,d,e) >= 0) or (q4(a,b,c,d,e) <= 0)

R = RDF # field for use for non-interval reals

def QuarticNDVolC(tol,B=None,v=None):
    # Here B is a list of 5 pairs b=[b[0],b[1]]
    if B is None:
        B = [[R(-1),R(1)] for _ in range(5)]
    if v is None:
        v = prod([b[1]-b[0] for b in B])  # the box's volume

    # quick exit if a>0 or e>0 or a+b+c+d+e>0 throughout:
    a1,b1,c1,d1,e1 = [I[0] for I in B]
    a2,b2,c2,d2,e2 = [I[1] for I in B]
    if a1 >=0:
        return 0
    if e1 >=0:
        return 0

    for x in [i*R(0.2) for i in range(1,21)]:
        if (((a1*x+b1)*x+c1)*x+d1)*x+e1 >= 0: return 0
        if (((a1*x-b2)*x+c1)*x-d2)*x+e1 >= 0: return 0

    if sum([b[0] for b in B]) >=0:
        return 0

    # evaluate at 2 of the 32 vertices (if neg def at these, must be neg def throughout):
    # corners = [[B[i][j] for i,j in enumerate(n.digits(base=2,padto=5))]
    #            for n in srange(32)]
    corners = [[a2,b2,c2,d2,e2],[a2,b1,c2,d1,e2]]
    if all([is_quartic_neg_def(q) for q in corners]):
        return v

    # add the range [0,v] if v is small
    if v < tol:
        return RIF(0,v)

    # else recurse
    v2 = v/32
    triples  = [[b[0],(b[0]+b[1])/2,b[1]] for b in B]
    subs = [[d[j:j+2] for d,j in zip(triples,n.digits(base=2,padto=5))] for n in srange(32)]
    return sum([QuarticNDVolC(tol,b,v2) for b in subs])

def QuarticVolSample(N):
    n0=n2=n4=0
    for i in xrange(N):
        a = RDF.random_element(-1,1)
        b = RDF.random_element(-1,1)
        c = RDF.random_element(-1,1)
        d = RDF.random_element(-1,1)
        e = RDF.random_element(-1,1)
        D = disc4(a,b,c,d,e)
        if D<=0:
            n2+=1
        else:
            H = h4(a,b,c,d,e)
            Q = q4(a,b,c,d,e)
            if H>=0 or Q<=0:
                n0 += 1
            if H<=0 and Q>=0:
                n4 += 1

    res = [1.0*n/N for n in [n0,n2,n4]]
    rpos = 1-res[0]/2
    print("not negative definite: %s" % rpos)
    return res

def GenQuarticVolSample(N):
    n0=n2=n4=0
    for i in xrange(N):
        # coeffs of quartic on RHS:
        a = RDF.random_element(-1,1)
        b = RDF.random_element(-1,1)
        c = RDF.random_element(-1,1)
        d = RDF.random_element(-1,1)
        e = RDF.random_element(-1,1)

        # coeffs of cross terms:
        l = RDF.random_element(-1,1)
        m = RDF.random_element(-1,1)
        n = RDF.random_element(-1,1)

        # complete the square:
        a = 4*a-l*l
        b = 4*b-2*l*m
        c = 4*c-m*m-2*l*n
        d = 4*d-2*m*n
        e = 4*e-n*n

        D = disc4(a,b,c,d,e)
        if D<=0:
            n2+=1
        else:
            H = h4(a,b,c,d,e)
            Q = q4(a,b,c,d,e)
            if H>=0 or Q<=0:
                n0 += 1
            if H<=0 and Q>=0:
                n4 += 1

    res = [1.0*n/N for n in [n0,n2,n4]]
    rpos = 1-res[0]/2
    print("not negative definite: %s" % rpos)
    return res

# Generalized quartic Montecarlo:

# sage: GenQuarticVolSample(10^4)
# not negative definite: 0.875200000000000
# [0.249600000000000, 0.708900000000000, 0.0415000000000000]
# sage: GenQuarticVolSample(10^5)
# not negative definite: 0.873305000000000
# [0.253390000000000, 0.706120000000000, 0.0404900000000000]
# sage: GenQuarticVolSample(10^6)
# not negative definite: 0.873861000000000
# [0.252278000000000, 0.706626000000000, 0.0410960000000000]
# sage: GenQuarticVolSample(10^7)
# not negative definite: 0.873775450000000
# [0.252449100000000, 0.706262900000000, 0.0412880000000000]
# sage: GenQuarticVolSample(10^8)
# not negative definite: 0.873742745000000
# [0.252514510000000, 0.706258520000000, 0.0412269700000000]

# Disc4>0:  (0.0128528225806451, 0.677419354838710), diameter 0.664566532258065
#           (0.0711827431955645, 0.523114604334678), diameter 0.451931861139113
#
# Disc4,negH4, Q4>0:
#Interval (0.000000000000000, 0.989501953125000), diameter 0.989501953125000
# tol 10^-4, 1m32s:
#Interval (0.000770568847656250, 0.541664123535157), diameter 0.540893554687500

def quartic_densities(tol):
    B0 = base_box(5)
    r04 = Fvold(5,Disc4,tol)
    print "0 or 4 real roots:"
    show(r04)
    r2 = 1-r04
    print "2 real roots:"
    show(r2)
    r4 = FFvol(B0,[Disc4,negH4,Q4],tol)/32
    print "4 real roots:"
    show(r4)
    r0 = r04-r4
    print "0 real roots:"
    show(r0)
    rneg = r0/2 # negative definite
    rpos = 1-rneg # not negative definite
    print "not negative definite:"
    show(rpos)
    return (rpos,r0,r2,r4)

def quartic_densities2(tol):
    B0 = base_box(5)
    r0, r2, r4 = QuarticVol(B0,tol)/32
    print "0 real roots:"
    show(r0)
    print "2 real roots:"
    show(r2)
    print "4 real roots:"
    show(r4)
    rneg = r0/2 # negative definite
    rpos = 1-rneg # not negative definite
    print "not negative definite:"
    show(rpos)
    return (rpos,r0,r2,r4)

def quartic_densities3(tol):
    B0 = base_box(5)
    rneg = QuarticNDVol(B0,tol)/32
    rpos = 1-rneg # not negative definite
    print "not negative definite:"
    show(rpos)
    return rpos

def quartic_densities3C(tol):
    rneg = QuarticNDVolC(R(tol))/32
    rpos = 1-rneg # not negative definite
    print "not negative definite:"
    show(rpos)
    return rpos

def quartic_densities4(tol):
    rneg = QuarticNDVolShell(tol)/32
    rpos = 1-rneg # not negative definite
    print "not negative definite:"
    show(rpos)
    return rpos


"""
Results of the python programs here and the C progams in boxes.cc:

Expecting density 0.874 for "not negative definite"

Sampling, 10^6 points: 0.8740745
                       0.8739535
                       0.8740895
                       0.8736505 (16s)
Sampling, 10^7 points: 0.87413925 (2m41s)


With tolerance 0.001:

sage: time res = quartic_densities2(0.001)
0 real roots:
(0.0124511718750000, 0.683349609375000), diameter 0.670898437500000
2 real roots:
(0.316650390625000, 0.987548828125000), diameter 0.670898437500000
4 real roots:
(0.000000000000000, 0.670898437500000), diameter 0.670898437500000
not negative definite:
(0.658325195312500, 0.993774414062500), diameter 0.335449218750000
CPU times: user 4.68 s, sys: 209 ms, total: 4.89 s

With tolerance 0.0001:

sage: time res = quartic_densities2(0.0001)
0 real roots:
(0.0687408447265625, 0.528121948242188), diameter 0.459381103515625
2 real roots:
(0.471878051757812, 0.931259155273438), diameter 0.459381103515625
4 real roots:
(0.000000000000000, 0.459381103515625), diameter 0.459381103515625
not negative definite:
(0.736137390136718, 0.965629577636719), diameter 0.229492187500000
CPU times: user 1min 42s, sys: 228 ms, total: 1min 42s

With tolerance 0.0001:

sage: time res = quartic_densities2(0.00001)
0 real roots:
(0.133889079093933, 0.424112200737000), diameter 0.290223121643066
2 real roots:
(0.570640802383422, 0.860863924026490), diameter 0.290223121643066
4 real roots:
(0.00524699687957763, 0.295470118522645), diameter 0.290223121643066
not negative definite:
(0.787943899631500, 0.933055460453034), diameter 0.145111560821533
CPU times: user 38min 2s, sys: 3.28 s, total: 38min 5s

Neg Def only (quartic_densities4(tol)):
10^-3: 1.1s,  (0.774949596, 0.993573588), diameter 0.21862399
10^-4: 30s,   (0.802309097, 0.964721679), diameter 0.162412
10^-5: 11m53s (0.826131912, 0.932004682), diameter 0.105872
10^-6: 11m53s (0.826131912, 0.932004682), diameter 0.105872
old:
10^-7: 4h24m  (0.842790509, 0.908747432), diameter 0.0659569

Convexity version
10^-3: 5s, (0.770751953125000, 0.948852539062500), diameter 0.1781
10^-4: 2m, (0.782096862792968, 0.914749145507813), diameter 0.1326
10^-5: 53m,(0.788767337799072, 0.895013689994813), diameter 0.1062

New Convexity version
2^-13:
(0.835123062133789, 0.914749145507813), diameter 0.0796260833740234
CPU times: user 1min 51s, sys: 225 ms, total: 1min 51s
(0.853896081447601, 0.895013689994813), diameter 0.0411176085472107
CPU times: user 33min 39s, sys: 2.87 s, total: 33min 42s
(0.863508559763431, 0.884636919945479), diameter 0.0211283601820469

2^-16 (7m):
(0.853896081447601, 0.894989252090455), diameter 0.0410931706428528
2^-21 (1h56m)
(0.863508559763431, 0.884634776040912), diameter 0.0211262162774801

2^-26
(0.868331281759310, 0.879372696275823), diameter 0.0110414145165123

C program: (use tolerance 1 mod 5)
time echo 21 | ./boxes (0.8s)
lower bound = 0.864183
upper bound = 0.883735
middle value = 0.873959
error bound  = 0.00977624

time echo 26 | ./boxes (2m5s)
lower bound = 0.868672
upper bound = 0.878928
middle value = 0.8738
error bound  = 0.0051277

time echo 31 | ./boxes (34m54s)
lower bound = 0.870914
upper bound = 0.876517
middle value = 0.873715 [so 0.871, 0.872, 0.873, 0.874, 0.875, 0.876, 0.877]
error bound  = 0.00280155

time echo 36 | ./boxes (623m=10h23m)
lower bound = 0.872033
upper bound = 0.875314
middle value = 0.873674   [so 0.872, 0.873, 0.874, 0.875]
error bound  = 0.00164025

time echo 41 | ./boxes (1088m=18h8m)
lower bound = 0.872193
upper bound = 0.875139
middle value = 0.873666  [so 0.872, 0.873, 0.874, 0.875]
error bound  = 0.00147275


time echo 35 | ./boxes (13h36m)
lower bound = 0.871948
upper bound = 0.875422
middle value = 0.873685
error bound  = 0.00173744

$ time echo 46 | ./boxes (14d 23h)
Input log_2-tolerance: tolerance = 1.42109e-14
res[0] = 13.9628, res[1] = 2.00596
lower bound = 0.872673
upper bound = 0.874627
middle value = 0.87365
error bound  = 0.000977271

"""
