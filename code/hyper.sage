def make_vinci_input(degree, depth, prefix):
    n = degree
    out = file("%s.ine" % prefix, mode='w')
    out.write("Degree %s, depth %s\n" % (degree, depth))
    out.write("H-representation\n")
    out.write("begin\n")
    nhyp = 2*(n+1) + 2 + len(list(QQ.range_by_height(2,depth+1)))

    #  output data size and type:
    out.write("%s %s integer\n" %(nhyp, n+2))

    #  output 2*(n+1) hyperplanes defining box:
    out.write("1  2" + " 0"*n + "\n")
    out.write("0 -1" + " 0"*n + "\n")
    for i in range(1,n):
        out.write("1 " + "0 "*i + " 2" + " 0"*(n-i) + "\n")
        out.write("1 " + "0 "*i + "-2" + " 0"*(n-i) + "\n")
    out.write("1" + " 0"*n + "  2\n")
    out.write("0" + " 0"*n + " -1\n")

    # output conditions for +1 and -1:
    out.write("0" + " -1"*(n+1) + "\n")
    out.write("0" + " -1 1"*(n//2) + " -1\n")

    # output conditions for rationals of height 2..depth:
    for r in QQ.range_by_height(2,depth+1):
        u = r.numerator()
        v = r.denominator()
        out.write("0")
        for i in range(n+1):
            out.write(" %s" % (-(u**i)*(v**(n-i))))
        out.write("\n")
    out.write("end\n")
    out.close()
