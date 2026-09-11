/* direct_analysis.m -- determine ALL rational effective divisors of degree D on X = X_1(N) when
   rk J(Q) = 0, J(Q) = ClCusp_Q (DEHMZ) and gon_Q X > D (so each class has at most one effective divisor).
   Method ("direct analysis over F_p, then over Q", cf. DEHMZ Sections 5.2/6 and the quartic paper):
   1. Parametrise J(Q) = ClCusp_Q as Z^r / K where the r generators are the Galois orbits of cusps
      (mdmagma CuspOrbitsQ over F_{p_1}) and K is the kernel of Z^r -> Cl(X_{F_{p_1}}) (equal to the
      kernel of Z^r -> J(Q) because reduction is injective on torsion for odd p_1 not dividing N).
   2. For each prime p in Ps: S_p := { classes of effective F_p-divisors of degree D }.  A rational
      effective divisor E of degree D reduces to an effective F_p-divisor, so [E - D c0] mod p lies in
      S_p - [D c0].  Keep the classes c in J(Q) with red_p(c) + [D c0]_p in S_p for all p.
   3. For each surviving class, compute L(D c0 + gamma_c) over Q (gamma_c = cuspidal representative);
      dim 1 gives the unique effective divisor, which is reported (and tested for being an irreducible
      non-cuspidal point); dim 0 means the class was a false positive.
   Usage: magma -n -b N:=30 Ps:=7,11 D:=5 direct_analysis.m */
SetColumns(0);
if not assigned N then N := 30; elif Type(N) eq MonStgElt then N := StringToInteger(N); end if;
if not assigned Ps then Ps := [7, 11]; elif Type(Ps) eq MonStgElt then Ps := [StringToInteger(s) : s in Split(Ps, ",")]; end if;
if not assigned D then D := 5; elif Type(D) eq MonStgElt then D := StringToInteger(D); end if;
if not assigned MemGB then MemGB := 16; elif Type(MemGB) eq MonStgElt then MemGB := StringToInteger(MemGB); end if;
if not assigned MaxLift then MaxLift := 400; elif Type(MaxLift) eq MonStgElt then MaxLift := StringToInteger(MaxLift); end if;
SetMemoryLimit(MemGB*10^9);
AttachSpec("mdmagma/v2/mdmagma.spec");
t0 := Cputime();
XQ := MDX1(N, Rationals()); CQ := Curve(XQ);
cuspsQ := Cusps(XQ);
sigQ := AssociativeArray();
for c in cuspsQ do sg := CuspSignature(XQ, c); assert not IsDefined(sigQ, sg); sigQ[sg] := c; end for;
r := #cuspsQ;
printf "SETUP X_1(%o): %o Galois orbits of cusps over Q, time %o\n", N, r, Cputime(t0);

// per-prime data
data := [* *];
for p in Ps do
  X := MDX1(N, GF(p)); C := Curve(X);
  orbits := [Type(O) eq PlcCrvElt select Divisor(O) else O : O in CuspOrbitsQ(X)];   // uniform divisor type
  // order the orbits by signature so that all primes use the same ordering as cuspsQ
  ord := [];
  for c in cuspsQ do
    sg := CuspSignature(XQ, c);
    idx := [i : i in [1..#orbits] | CuspSignature(X, Support(orbits[i])[1]) eq sg];
    assert #idx eq 1; Append(~ord, idx[1]);
  end for;
  orbits := [orbits[i] : i in ord];
  assert &and[Degree(orbits[i]) eq Degree(cuspsQ[i]) : i in [1..r]];
  cusps := Cusps(X);
  c0 := Support([O : O in orbits | Degree(O) eq 1][1])[1];   // reduction of a Q-rational cusp
  Cl, m1, m2 := ClassGroup(C);
  Free := FreeAbelianGroup(r);
  h := hom< Free -> Cl | [m2(O - Degree(O)*Divisor(c0)) : O in orbits] >;
  G := Image(h);
  printf "PRIME %o: genus %o, Cl(X_Fp) invariants %o, image of ClCusp_Q: %o, time %o\n", p, Genus(X), Invariants(Cl), Invariants(G), Cputime(t0);
  // all effective divisors of degree D over F_p: multisets of places with degrees summing to D
  places := [Places(C, d) : d in [1..D]];
  printf "PRIME %o: places of degree 1..%o: %o\n", p, D, [#pl : pl in places];
  S := {};
  cnt := 0;
  for lambda in Partitions(D) do
    degs := Sort(Setseq(Seqset(lambda)));
    if exists{e : e in degs | #places[e] eq 0} then continue; end if;
    choices := [* *];
    for e in degs do
      k := #[x : x in lambda | x eq e];
      Append(~choices, [ &+[Divisor(x) : x in Sset] : Sset in Multisets(Seqset(places[e]), k) ]);
    end for;
    // stream over the cartesian product to save memory: classes only
    partialcl := [m2(DivisorGroup(C)!0)];
    for ch in choices do
      chcl := [m2(b) : b in ch];
      partialcl := [ a + b : a in partialcl, b in chcl ];
    end for;
    for g in partialcl do Include(~S, g); cnt +:= 1; end for;
    printf "PRIME %o: type %o done, %o divisors so far, %o distinct classes, time %o\n", p, lambda, cnt, #S, Cputime(t0);
  end for;
  Append(~data, <p, X, h, G, S, m2(D*Divisor(c0)), c0, m2, Cl>);
end for;

// parametrise J(Q) = Z^r / K using the first prime
p1, X1, h1, G1, S1, base1 := Explode(data[1]);
Free := Domain(h1);
K := Kernel(h1);
Qgrp, qmap := quo< Free | K >;
printf "J(Q) = ClCusp_Q parametrised: order %o, invariants %o (DEHMZ table for comparison)\n", #Qgrp, Invariants(Qgrp);
// maps Qgrp -> Cl_p for each prime (well defined since K = ker h1 = ker of reduction for every p by injectivity)
maps := [* *];
for dt in data do
  hp := dt[3];
  // check K is in the kernel of hp
  assert &and[ hp(Free!k) eq Identity(Codomain(hp)) : k in Generators(K) ];
  Append(~maps, hom< Qgrp -> Codomain(hp) | [hp(g @@ qmap) : g in OrderedGenerators(Qgrp)] >);
end for;
cands := [];
for c in Qgrp do
  ok := true;
  for i in [1..#data] do
    if not (maps[i](c) + data[i][6]) in data[i][5] then ok := false; break; end if;
  end for;
  if ok then Append(~cands, c); end if;
end for;
// classes of the effective Q-rational CUSPIDAL divisors of degree D: multisets of cusp orbits
// (vectors in Z^r) with degrees summing to D; their classes are cuspidal candidates that need no lift.
i0 := [i : i in [1..r] | Degree(cuspsQ[i]) eq 1][1];
degsQ := [Degree(c) : c in cuspsQ];
cuspclasses := {};
ncuspdiv := 0;
procedure AddCusp(vec, remaining, start, ~cuspclasses, ~ncuspdiv)
  if remaining eq 0 then
    v := vec; v[i0] -:= D;
    Include(~cuspclasses, qmap(Free!v)); ncuspdiv +:= 1; return;
  end if;
  for i in [start..r] do
    if degsQ[i] le remaining then
      v := vec; v[i] +:= 1;
      AddCusp(v, remaining - degsQ[i], i, ~cuspclasses, ~ncuspdiv);
    end if;
  end for;
end procedure;
AddCusp([0 : i in [1..r]], D, 1, ~cuspclasses, ~ncuspdiv);
printf "CUSPIDAL: %o effective rational cuspidal divisors of degree %o in %o distinct classes; all are candidates: %o\n", ncuspdiv, D, #cuspclasses, cuspclasses subset Seqset(cands);
noncusp := [c : c in cands | c notin cuspclasses];
// known quintic points (van Hoeij) for N = 28, 30: their classes in J(Q), via reduction at p_1
Qx<x> := PolynomialRing(Rationals());
known := [];
if N eq 28 then known := [ <x^5-x^4-2*x^3-x^2+2*x+2, func<t | t^3-1>> ]; end if;
if N eq 30 then known := [ <x^5+x^4-3*x^3+3*x+1, func<t | 2*t^4+t^3-6*t^2+4*t+4>>,
                           <x^5+x^4-7*x^3+x^2+12*x+3, func<t | (3*t^4+7*t^3+6*t^2+11*t-73)/53>> ]; end if;
knownclasses := {};
if #known gt 0 then
  X1c := data[1][2]; C1 := Curve(X1c); m2_1 := data[1][8]; base1 := data[1][6];
  diamonds := [a : a in [1..(N div 2)] | GCD(a,N) eq 1];
  for i in [1..#known] do
    f, yf := Explode(known[i]); Kf<al> := NumberField(f); OK := MaximalOrder(Kf);
    x0 := al; y0 := yf(al); Dred := DivisorGroup(C1)!0;
    for Pf in Decomposition(OK, p1) do
      P := Pf[1]; Cp, mC := Completion(Kf, P : Precision := 40); R := Integers(Cp); k, mk := ResidueClassField(R);
      vmin := Min([Valuation(x0, P), Valuation(y0, P), 0]); pi := UniformizingElement(P); sc := pi^(-vmin);
      coords := [x0*sc, y0*sc, Kf!sc]; red := [ mk(R ! mC(cc)) : cc in coords ];
      pl := Places(C1(k) ! red); assert #pl eq 1; Dred +:= Divisor(pl[1]);
    end for;
    assert Degree(Dred) eq D;
    for a in diamonds do
      Da := DiamondOperator(X1c, a, Dred);
      cl := (m2_1(Da) - base1) @@ maps[1];
      Include(~knownclasses, cl);
    end for;
  end for;
  printf "KNOWN points: %o orbits, %o distinct classes of their diamond translates; all among the candidates: %o\n", #known, #knownclasses, knownclasses subset Seqset(cands);
end if;
noncusp := [c : c in noncusp | c notin knownclasses];
printf "MATCHED_KNOWN: after removing the classes of the known points, %o non-cuspidal candidate classes remain\n", #noncusp;
printf "CANDIDATES_NONCUSPIDAL: %o candidate classes remain after removing the cuspidal classes (these are lifted to Q)\n", #noncusp;
printf "CANDIDATES: %o classes of J(Q) whose reduction is the class of an effective degree-%o divisor for all p in %o, time %o\n", #cands, D, Ps, Cputime(t0);

// short representatives of classes: reduce modulo the relation lattice K (full rank r) by CVP
Kbasis := Matrix(Integers(), [Eltseq(Free!k) : k in Generators(K)]);
Lat := LatticeWithBasis(LLL(Kbasis));
function ShortRep(vec)
  w := ClosestVector(Lat, Vector(Rationals(), vec));
  return [vec[i] - Integers()!w[i] : i in [1..#vec]];
end function;
// lift over Q
c0Q := cuspsQ[[i : i in [1..r] | Degree(cuspsQ[i]) eq 1][1]];
nlift := 0; npoints := 0; ncusp := 0; nempty := 0;
for c in noncusp do
  nlift +:= 1; if nlift mod 50 eq 0 then printf "LIFT progress %o/%o time %o\n", nlift, #noncusp, Cputime(t0); end if;
  v := ShortRep(Eltseq(c @@ qmap));
  gammaQ := &+[v[i]*Divisor(cuspsQ[i]) : i in [1..r]];
  gammaQ -:= Degree(gammaQ)*Divisor(c0Q);
  Dlift := D*Divisor(c0Q) + gammaQ;
  V, mV := RiemannRochSpace(Dlift);
  if Dimension(V) eq 0 then nempty +:= 1; continue; end if;
  if Dimension(V) ge 2 then printf "WARNING class %o has l = %o (a degree <= %o function?)\n", v, Dimension(V), D; continue; end if;
  E := Dlift + Divisor(mV(V.1));
  assert IsEffective(E) and Degree(E) eq D;
  sup, mul := Support(E);
  iscusp := [IsCusp(XQ, s) : s in sup];
  if &and iscusp then ncusp +:= 1;
  else
    npoints +:= 1;
    printf "POINT class %o: support degrees %o, multiplicities %o, cuspidal flags %o\n", v, [Degree(s) : s in sup], mul, iscusp;
    for i in [1..#sup] do if not iscusp[i] then
      printf "POINT   non-cuspidal component of degree %o: j min poly %o\n", Degree(sup[i]), MinimalPolynomial(jInvariant(XQ, sup[i]));
    end if; end for;
  end if;
end for;
printf "RESULT N=%o D=%o: %o candidate classes; %o with no effective divisor (false positives), %o all-cuspidal effective divisors, %o effective divisors with a non-cuspidal component; time %o\n", N, D, #cands, nempty, ncusp, npoints, Cputime(t0);
print "DIRECT_DONE";
quit;
