/* analyze_survivors.m (v2) -- X = X_1(N) over F_p (M=1), rank 0, J(Q) = ClCusp_Q (DEHMZ).
   (1) reconstruct survivors (file SURV: one SURVIVOR_DATA expression per line);
   (2) reduce known quintic points (N=28,30, van Hoeij) mod every prime above p; match up to diamonds;
   (3) for each unmatched survivor D and each effective cuspidal F_p-divisor C of degree 5-deg D:
       test [D + C - 5 c0] in G := image of ClCusp_Q in Cl(X_Fp) (CuspidalClassGroupQ);
   (4) for classes in G: lift to Q using the cusp signatures (mdmagma CuspSignature identifies the
       Q-orbit of each F_p cusp orbit), and compute the Riemann-Roch space of the lifted degree-5
       class over Q: dim 0 -> no rational effective divisor in the class; dim 1 -> the unique
       effective divisor is printed and tested for being an irreducible non-cuspidal degree-5 point;
       dim >= 2 -> the class contains a fixed rational component (no degree-5 function exists), so
       no irreducible degree-5 point.
   Usage: magma -n -b N:=28 p:=3 SURV:=data/surv_28_3.txt analyze_survivors.m */
SetColumns(0);
if not assigned N then N := 28; elif Type(N) eq MonStgElt then N := StringToInteger(N); end if;
if not assigned p then p := 3; elif Type(p) eq MonStgElt then p := StringToInteger(p); end if;
if not assigned SURV then SURV := "data/surv_28_3.txt"; end if;
if not assigned D then D := 5; elif Type(D) eq MonStgElt then D := StringToInteger(D); end if;
AttachSpec("mdmagma/v2/mdmagma.spec");
X := MDX1(N, GF(p)); C := Curve(X);
XQ := MDX1(N, Rationals()); CQ := Curve(XQ);
printf "SETUP X_1(%o) over F_%o, genus %o\n", N, p, Genus(X);

// ---- (1) survivors ----
lines := [l : l in Split(Read(SURV), "\n") | #l gt 0];
survivors := [];
for l in lines do
  data := eval l;
  Dv := DivisorGroup(C) ! 0;
  for item in data do
    dg, mult, defpoly, coords := Explode(item);
    K := ext<GF(p) | Polynomial(GF(p), defpoly)>;
    pt := C(K) ! [K!c : c in coords];
    pl := Places(pt); assert #pl eq 1; assert Degree(pl[1]) eq dg;
    Dv +:= mult*Divisor(pl[1]);
  end for;
  Append(~survivors, Dv);
end for;
printf "SURVIVORS reconstructed: %o, degrees %o\n", #survivors, [Degree(s) : s in survivors];

// ---- (2) known points ----
Qx<x> := PolynomialRing(Rationals());
known := [];
if N eq 28 then known := [ <x^5-x^4-2*x^3-x^2+2*x+2, func<t | t^3-1>> ]; end if;
if N eq 30 then known := [ <x^5+x^4-3*x^3+3*x+1, func<t | 2*t^4+t^3-6*t^2+4*t+4>>,
                           <x^5+x^4-7*x^3+x^2+12*x+3, func<t | (3*t^4+7*t^3+6*t^2+11*t-73)/53>> ]; end if;
diamonds := [a : a in [1..(N div 2)] | GCD(a,N) eq 1];
reductions := [];
for i in [1..#known] do
  f, yf := Explode(known[i]);
  K<a> := NumberField(f); OK := MaximalOrder(K);
  x0 := a; y0 := yf(a);
  Dred := DivisorGroup(C) ! 0;
  for Pf in Decomposition(OK, p) do
    P := Pf[1];
    Cp, mC := Completion(K, P : Precision := 40);
    R := Integers(Cp); k, mk := ResidueClassField(R);
    v := Min([Valuation(x0, P), Valuation(y0, P), 0]);
    pi := UniformizingElement(P); s := pi^(-v);
    coords := [x0*s, y0*s, K!s];
    assert Min([Valuation(cc, P) : cc in coords]) eq 0;
    red := [ mk(R ! mC(cc)) : cc in coords ];
    pt := C(k) ! red; pl := Places(pt); assert #pl eq 1;
    Dred +:= Divisor(pl[1]);
    printf "KNOWN point %o: prime above %o of residue degree %o -> place of degree %o\n", i, p, InertiaDegree(P), Degree(pl[1]);
  end for;
  assert Degree(Dred) eq D;
  Append(~reductions, <i, Dred>);
end for;
matched := [false : s in survivors];
for r in reductions do
  for a in diamonds do
    Da := DiamondOperator(X, a, r[2]);
    for j in [1..#survivors] do
      if Da eq survivors[j] then matched[j] := true; printf "MATCH survivor %o = <%o> * reduction of known point %o\n", j, a, r[1]; end if;
    end for;
  end for;
end for;
printf "MATCHED %o of %o survivors\n", #[m : m in matched | m], #survivors;

// ---- (3) cuspidal-group test ----
unmatched := [j : j in [1..#survivors] | not matched[j]];
if #unmatched eq 0 then print "ANALYZE_DONE (all survivors are reductions of known points)"; quit; end if;

orbitsFp := [Type(O) eq PlcCrvElt select Divisor(O) else O : O in CuspOrbitsQ(X)];   // F_p-divisors, one per Galois orbit over Q
Cl, m1, m2 := ClassGroup(C);
Free := FreeAbelianGroup(#orbitsFp);
cusps := Cusps(X);
// base cusp: must be the reduction of a Q-RATIONAL cusp, i.e. lie in a Galois orbit of degree 1
c0 := Support([O : O in orbitsFp | Degree(O) eq 1][1])[1];
gens := [m2(O - Degree(O)*Divisor(c0)) : O in orbitsFp];
h := hom< Free -> Cl | gens >;
G := Image(h);
printf "G = image of ClCusp_Q in Cl(X_Fp): invariants %o (expected order of J(Q)_tors from DEHMZ table)\n", Invariants(G);
// Q-side: cusps of XQ and their signatures, matched to the F_p orbits by signature
cuspsQ := Cusps(XQ);
sigQ := AssociativeArray();
for c in cuspsQ do sg := CuspSignature(XQ, c); assert not IsDefined(sigQ, sg); sigQ[sg] := c; end for;
orbitQ := [];   // orbitQ[i] = Q-place corresponding to orbitsFp[i]
for O in orbitsFp do
  supp := Support(O); sg := CuspSignature(X, supp[1]);
  assert IsDefined(sigQ, sg); c := sigQ[sg]; assert Degree(c) eq Degree(O);
  Append(~orbitQ, c);
end for;
c0Q := sigQ[CuspSignature(X, c0)]; assert Degree(c0Q) eq 1;
printf "Q-orbits matched to F_p-orbits by cusp signature: %o orbits\n", #orbitQ;

for j in unmatched do
  Dv := survivors[j]; k := D - Degree(Dv);
  if k eq 0 then Cs := [DivisorGroup(C)!0];
  else
    Cs := [];
    for lambda in Partitions(k) do
      ok := true; choices := [* *];
      for e in Sort(Setseq(Seqset(lambda))) do
        ce := [Divisor(c) : c in cusps | Degree(c) eq e];
        if #ce eq 0 then ok := false; break; end if;
        mlt := #[t : t in lambda | t eq e];
        Append(~choices, [ &+[d : d in S] : S in Multisets(Seqset(ce), mlt) ]);
      end for;
      if not ok then continue; end if;
      partial := [DivisorGroup(C)!0];
      for ch in choices do partial := [ a + b : a in partial, b in ch ]; end for;
      Cs cat:= partial;
    end for;
  end if;
  inG := [Cc : Cc in Cs | m2(Dv + Cc - D*Divisor(c0)) in G];
  printf "UNMATCHED survivor %o (degree %o): %o cuspidal complements, %o give a class in G\n", j, Degree(Dv), #Cs, #inG;
  for Cc in inG do
    g := m2(Dv + Cc - D*Divisor(c0));
    coeffs := Eltseq(g @@ h);
    gammaQ := &+[coeffs[i]*Divisor(orbitQ[i]) : i in [1..#coeffs]];
    gammaQ -:= Degree(gammaQ)*Divisor(c0Q);
    Dlift := D*Divisor(c0Q) + gammaQ;
    V, mV := RiemannRochSpace(Dlift);
    printf "LIFT survivor %o complement %o: class coefficients %o, dim L(lift) = %o\n", j, Cc, coeffs, Dimension(V);
    if Dimension(V) eq 1 then
      E := Dlift + Divisor(mV(V.1));
      assert IsEffective(E) and Degree(E) eq D;
      sup, mul := Support(E);
      printf "LIFT survivor %o: unique effective divisor of degree %o in the class: support degrees %o, multiplicities %o, cuspidal? %o\n", j, D, [Degree(s) : s in sup], mul, [IsCusp(XQ, s) : s in sup];
      if #sup eq 1 and mul[1] eq 1 and not IsCusp(XQ, sup[1]) then
        printf "NEW_POINT survivor %o: irreducible non-cuspidal degree-%o point found! j-invariant minimal polynomial: %o\n", j, D, MinimalPolynomial(jInvariant(XQ, sup[1]));
      end if;
    end if;
  end for;
end for;
print "ANALYZE_DONE";
quit;
