
Binom := func<n,r|&*[n+1-i: i in [1..r]]/Factorial(r)>;
MC := MonomialCoefficient;

// Computing the sets Gamma

function HasSmoothPointTwo(i,f:Proj := false)
  PP := Parent(f);
  f1 := Derivative(f,1);
  f2 := Derivative(f,2);
  for x0,z0 in GF(2) do
    if Evaluate(f,[x0,z0]) eq 0 and 
        (Evaluate(f1,[x0,z0]) ne 0 or Evaluate(f2,[x0,z0]) ne 0) then 
      return true;
    end if;
  end for;
  if Proj then
    x := PP.1;
    z := PP.2;
    ii := Integers()!(i/2);
    if MC(f,x^i) eq 0 and (MC(f,x^(i-1)) ne 0 or MC(f,x^ii*z) ne 0) then
       return true;
    end if;
    f := Evaluate(f,[x,z+x^ii]);
    if MC(f,x^i) eq 0 and (MC(f,x^(i-1)) ne 0 or MC(f,x^ii*z) ne 0) then
       return true;
    end if;
  end if;
  return false;
end function;

function GammaPlusTwo(i)
  p := 2;
  print "GammaPlus with p = 2 and i =",i;
  P<x> := PolynomialRing(GF(p));
  PP<X,Z> := PolynomialRing(GF(p),2);
  V1 := RSpace(GF(p),Ceiling(i/2));
  V2 := RSpace(GF(p),i);
  if IsEven(i) then  
    forms := [Z^2 + Evaluate(P!(Eltseq(v1) cat [1]),X)*Z 
                  - Evaluate(P!Eltseq(v2),X): v1 in V1,v2 in V2];
  else
    forms := [Z^2 + Evaluate(P!Eltseq(v1),X)*Z 
                  - Evaluate(P!(Eltseq(v2) cat [1]),X): v1 in V1,v2 in V2];
  end if;
  ans := [f : f in forms | not HasSmoothPointTwo(i,f)];
  assert #ans eq [0,0,6,16,64,128][i];
  return ans;
end function;

function GammaMinusTwo(i)
  p := 2;
  if IsOdd(i) then return GammaPlusTwo(i); end if;
  print "GammaMinus with p = 2 and i =",i;
  P<x> := PolynomialRing(GF(p));
  PP<X,Z> := PolynomialRing(GF(p),2);
  V1 := RSpace(GF(p),Ceiling(i/2));
  V2 := RSpace(GF(p),i);
  forms := [Z^2 + Evaluate(P!(Eltseq(v1) cat [1]),X)*Z 
                - Evaluate(P!(Eltseq(v2) cat [1]),X): v1 in V1,v2 in V2];
  ans := [f : f in forms | not HasSmoothPointTwo(i,f)];
  PP2 := PolynomialRing(GF(p^2),2);
  ans := [f : f in ans | IsIrreducible(PP2!f)];
  assert #ans eq [0,0,0,0,0,64][i];
  return ans;
end function;

function HasSmoothPoint(p,i,f:Proj := false)
  assert p ne 2;
  if f eq 0 then return false; end if;
  Z := Integers();
  if exists{x0 : x0 in GF(p) | LegendreSymbol(Z!Evaluate(f,x0),p) eq 1} 
      or exists{r : r in Roots(f) | r[2] eq 1 } then
    return true; 
  end if;
  if Proj then
    if LegendreSymbol(Z!Coefficient(f,i),p) eq 1 
        or (Coefficient(f,i) eq 0 and Coefficient(f,i-1) ne 0) then
      return true;
    end if;
  end if;
  return false;
end function;

function GammaPlus(i,p)
//  assert i le 8;
  if p eq 2 then return GammaPlusTwo(i); end if;
//  if i le 6 and p gt 13 then return []; end if; 
  if i le 6 and p gt 20 then return []; end if; 
  P<x> := PolynomialRing(GF(p));
  ans := [];
  if p gt i-3 and i gt 3 and GCD(i,p) eq 1 and IsEven(i) then
    print "entering new code";
    ff0 := &*[x-j : j in [0..i-3]]; // *(x+&+[j : j in [0..i-3]]);
    ff := [&*[x-j: j in [0..i-3]| j ne k]: k in [0..i-3]];
    ff := [ff[k+1]/Evaluate(ff[k+1],k): k in [0..i-3]];
    print Matrix(i-2,i-2,[Evaluate(f,k): k in [0..i-3],f in ff]);
    ns := [x : x in GF(p) | LegendreSymbol(Integers()!x,p) ne 1];
    assert #ns eq (p+1)/2;
    V := RSpace(Integers(#ns),i-2);
    u := Minimum([Integers()!x: x in ns | x ne 0]);
    s := Coefficient(ff0,i-3);
    t := Coefficient(ff0,i-4)-s^2;
    rr := [1..Integers()!((p-1)/2)];
//print ff0;
//print ff;
    for kappa in [0,1,u] do
      temp := [];
      print "kappa =",kappa;
      time for v in V do
        w := [ns[(Integers()!vj)+1]: vj in Eltseq(v)];
        f := (x^2-s*x+kappa-t)*ff0 + &+[w[j]*ff[j] : j in [1..i-2]];
        assert Coefficient(f,i) eq 1;
        assert Coefficient(f,i-1) eq 0;
        assert Coefficient(f,i-2) eq kappa;
        if not HasSmoothPoint(p,i,f) then
          Append(~temp,f);
        end if;
      end for;
      if kappa ne 0 then 
        ans cat:= [Evaluate(f,r*x)/r^i : f in temp,r in rr];
      else
        ans cat:= temp;
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  elif p ge i and i gt 2 and GCD(i,p) eq 1 then 
    print "entering recent code";
    ff0 := &*[x-j : j in [0..i-2]]*(x+&+[j : j in [0..i-2]]);
    ff := [&*[x-j: j in [0..i-2]| j ne k]: k in [0..i-2]];
    ff := [ff[k+1]/Evaluate(ff[k+1],k): k in [0..i-2]];
    print Matrix(i-1,i-1,[Evaluate(f,k): k in [0..i-2],f in ff]);
    ns := [x : x in GF(p) | LegendreSymbol(Integers()!x,p) ne 1];
    assert #ns eq (p+1)/2;
    V := RSpace(Integers(#ns),i-1);
    for v in V do
      w := [ns[(Integers()!vj)+1]: vj in Eltseq(v)];
      f := ff0 + &+[w[j]*ff[j] : j in [1..i-1]];
      assert Coefficient(f,i) eq 1;
      assert Coefficient(f,i-1) eq 0;
      if not HasSmoothPoint(p,i,f) then
        Append(~ans,f);
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  elif GCD(i,p) eq 1 then
    V := RSpace(GF(p),i-1);
    for v in V do
      f := P!(Eltseq(v) cat [0,1]);
      if not HasSmoothPoint(p,i,f) then
        Append(~ans,f);
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  else
    V := RSpace(GF(p),i);
    for v in V do
      f := P!(Eltseq(v) cat [1]);
      if not HasSmoothPoint(p,i,f) then
        Append(~ans,f);
      end if;
    end for;
  end if;

// print ans;
print p,i,#ans;

if p eq 3 and i le 12 then assert #ans eq [0,0,1,6,21,64,192,576,1728,5184,15552,46656][i]; end if;
if p eq 5 and i le 12 then assert #ans eq [0,0,0,5,47,250,1285,6440,32210,161051,0,0][i]; end if;
if p eq 7 and i le 10 then assert #ans eq [0,0,0,0,49,392,2992,21126,148386,1038849][i]; end if;
if p eq 11 and i le 10 then assert #ans eq [0,0,0,0,11,220,3762,43032,490347,5405422][i]; end if;
if p eq 13 and i le 10 then assert #ans eq [0,0,0,0,0,104,2691,38064,535028,6988605][i]; end if;
if p eq 17 and i le 10 then assert #ans eq [0,0,0,0,0,  0,816,15810,350540,6075868][i]; end if;
if p eq 19 and i le 10 then assert #ans eq [0,0,0,0,0,  0,171,8436,229406,4473930][i]; end if;

return ans;
end function;

function GammaMinus(i,p)
//  assert i le 8;
  if p eq 2 then return GammaMinusTwo(i); end if;
//  if i le 6 and p gt 11 then return []; end if; 
  if i le 6 and p gt 20 then return []; end if; 
  for u0 in [1..p] do
    u := u0;
    if LegendreSymbol(u,p) eq -1 then break; end if;
  end for;
  P<x> := PolynomialRing(GF(p));
  ans := [];
  if p gt i-3 and i gt 3 and GCD(i,p) eq 1 and IsEven(i) then
    print "entering new code";
    ff0 := &*[x-j : j in [0..i-3]]; // *(x+&+[j : j in [0..i-3]]);
    ff := [&*[x-j: j in [0..i-3]| j ne k]: k in [0..i-3]];
    ff := [ff[k+1]/Evaluate(ff[k+1],k): k in [0..i-3]];
    print Matrix(i-2,i-2,[Evaluate(f,k): k in [0..i-3],f in ff]);
    ns := [x : x in GF(p) | LegendreSymbol(Integers()!x,p) ne 1];
    assert #ns eq (p+1)/2;
    V := RSpace(Integers(#ns),i-2);
//    u := Minimum([Integers()!x: x in ns | x ne 0]);
    s := Coefficient(ff0,i-3);
    t := u*(Coefficient(ff0,i-4)-s^2);
    rr := [1..Integers()!((p-1)/2)];
//print ff0;
//print ff;
    for kappa in [0,1,u] do
      temp := [];
      print "kappa =",kappa;
      time for v in V do
        w := [ns[(Integers()!vj)+1]: vj in Eltseq(v)];
        f := (u*x^2-s*u*x+kappa-t)*ff0 + &+[w[j]*ff[j] : j in [1..i-2]];
        assert Coefficient(f,i) eq u;
        assert Coefficient(f,i-1) eq 0;
        assert Coefficient(f,i-2) eq kappa;
        if not HasSmoothPoint(p,i,f) and not IsSquare(u*f) then
          Append(~temp,f);
        end if;
      end for;
      if kappa ne 0 then 
        ans cat:= [Evaluate(f,r*x)/r^i : f in temp,r in rr];
      else
        ans cat:= temp;
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  elif p ge i and i gt 2 and GCD(i,p) eq 1 then 
    print "entering new code";
    ff0 := &*[x-j : j in [0..i-2]]*(x+&+[j : j in [0..i-2]]);
    ff := [&*[x-j: j in [0..i-2]| j ne k]: k in [0..i-2]];
    ff := [ff[k+1]/Evaluate(ff[k+1],k): k in [0..i-2]];
    print Matrix(i-1,i-1,[Evaluate(f,k): k in [0..i-2],f in ff]);
    ns := [x : x in GF(p) | LegendreSymbol(Integers()!x,p) ne 1];
    assert #ns eq (p+1)/2;
    V := RSpace(Integers(#ns),i-1);
    for v in V do
      w := [ns[(Integers()!vj)+1]: vj in Eltseq(v)];
      f := u*ff0 + &+[w[j]*ff[j] : j in [1..i-1]];
      assert Coefficient(f,i) eq u;
      assert Coefficient(f,i-1) eq 0;
      if not HasSmoothPoint(p,i,f) and not IsSquare(u*f) then
        Append(~ans,f);
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  elif GCD(i,p) eq 1 then
    V := RSpace(GF(p),i-1);
    for v in V do
      f := P!(Eltseq(v) cat [0,u]);
      if not HasSmoothPoint(p,i,f) and not IsSquare(u*f) then 
        Append(~ans,f);
      end if;
    end for;
    ans := [Evaluate(f,x+b) : f in ans, b in GF(p)];
  else
    V := RSpace(GF(p),i);
    for v in V do
      f := P!(Eltseq(v) cat [u]);
      if not HasSmoothPoint(p,i,f) and not IsSquare(u*f) then 
        Append(~ans,f);
      end if;
    end for;
  end if;
print "*******",p,i,#ans;

if p eq  3 and i le 12 then assert #ans eq [0,0,0,0,0,37,0,495,0,4941,0,45927][i]; end if;
if p eq  5 and i le 10 then assert #ans eq [0,0,0,0,0,145,0,5820,0,157926][i]; end if;
if p eq  7 and i le 10 then assert #ans eq [0,0,0,0,0,196,0,18928,0,1022119][i]; end if;
if p eq 11 and i le 10 then assert #ans eq [0,0,0,0,0,55,0,35442,0,5265106][i]; end if;
if p eq 13 and i le 10 then assert #ans eq [0,0,0,0,0, 0,0,29471,0,6721403][i]; end if;
if p eq 17 and i le 10 then assert #ans eq [0,0,0,0,0, 0,0,10404,0,5592150][i]; end if;
if p eq 19 and i le 10 then assert #ans eq [0,0,0,0,0, 0,0,5130,0,3793356][i]; end if;
if p eq 23 and i le 10 then assert #ans eq [0,0,0,0,0, 0,0,506,0,1419330][i]; end if;
if p eq 29 and i le 10 then assert #ans eq [0,0,0,0,0, 0,0,0,0,136416][i]; end if;

return ans;
end function;

