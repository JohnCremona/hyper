var('a','b','c')
assume(a>0)
assume(b>0)
assume(c>0)
assume(a<1)
assume(b<1)
assume(c<1)
r = integral(integral(integral(1,c,b^2/(4*a),1),a,b^2/4,1),b,0,1)
r = r.canonicalize_radical()
print("Probability of being positive definite on [0,1]^3: %s" % r)
# -1/6*log(2) + 31/36
# this only cover the box [0,1]^3 so gives the volume of the sub-box which are pos.def.;
# so the prob. of pos.def. is 1/4 of this and the prob of neg def is the same.
print("Probability of being definite:              %s" % (r/2))
# -1/12*log(2) + 31/72
print("Probability of being negative definite:     %s" % (r/4))
# -1/24*log(2) + 31/144
s=1-r/4
print("Probability of being not negative definite: %s" % s)
# 1/24*log(2) + 113/144
print("Numerically:                                %s" % s.n())
# 0.813603354745553
