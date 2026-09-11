/* direct_analysis_X11.m -- rational effective degree-D divisors on X = X_1(2,N), rank 0,
   J(Q)_tors = ClCusp_Q (DEHMZ Prop. "cusp_generate_2N", N/2 <= 16).  Same method as
   direct_analysis.m; Galois orbits of cusps over F_p identified by cusp signatures (valuations of
   u, v, b, c, 1-b-c, 4b^2+4bc-4b+c^2, x(kQ)), checked against the cuspidal closed points over Q.

   SCOPE.  The script enumerates the candidate classes and lifts to Q only those that contain NO
   effective rational cuspidal divisor; the cuspidal classes are reported but their linear systems
   are not computed.  So the output is the complete list of IRREDUCIBLE NON-CUSPIDAL degree-D
   points, not the complete list of effective degree-D divisors.  The two coincide when
   gon_Q X > D, since then every class holds at most one effective divisor (the case N = 20, 24
   for D = 5).  They do not coincide for N = 18, D = 5, where gon_Q X = 4: see pencils_2_18.m,
   which handles the cuspidal classes and finds 27 of them containing a moving pencil, each with a
   rational cusp as fixed part.
   Usage: magma -n -b N:=24 Ps:=5,7 D:=5 direct_analysis_X11.m */
SetColumns(0);
if not assigned N then N := 20; elif Type(N) eq MonStgElt then N := StringToInteger(N); end if;
if not assigned Ps then Ps := [3, 7]; elif Type(Ps) eq MonStgElt then Ps := [StringToInteger(s) : s in Split(Ps, ",")]; end if;
if not assigned D then D := 5; elif Type(D) eq MonStgElt then D := StringToInteger(D); end if;
if not assigned MemGB then MemGB := 16; elif Type(MemGB) eq MonStgElt then MemGB := StringToInteger(MemGB); end if;
if not assigned MaxLift then MaxLift := 400; elif Type(MaxLift) eq MonStgElt then MaxLift := StringToInteger(MaxLift); end if;
SetMemoryLimit(MemGB*10^9);
AttachSpec("mdmagma/v2/mdmagma.spec");
t0 := Cputime();
function SigFunctions(Y)
  FF := FunctionField(Curve(Y)); u := FF.1; v := FF.2;
  b, c := Explode([FF!f : f in Y`_coordinates]);
  E := EllipticCurve([0, c, 0, (1-b-c)*b, 0]); Q := E![b, b];
  fs := [u, v, b, c, 1-b-c, 4*b^2+4*b*c-4*b+c^2];
  for k in [2..(N div 2)] do kQ := k*Q; if kQ[3] ne 0 then Append(~fs, kQ[1]); end if; end for;
  return fs;
end function;
function Signature(fs, P) return [Valuation(f, P) : f in fs]; end function;

XQ := MDX11(2, N, Rationals()); CQ := Curve(XQ);
cuspsQ := Cusps(XQ); fsQ := SigFunctions(XQ);
sigQ := AssociativeArray();
for c in cuspsQ do sg := Signature(fsQ, c); assert not IsDefined(sigQ, sg); sigQ[sg] := c; end for;
r := #cuspsQ;
printf "SETUP X_1(2,%o): genus %o, %o Galois orbits of cusps over Q (degrees %o), time %o\n", N, Genus(XQ), r, Sort([Degree(c) : c in cuspsQ]), Cputime(t0);

data := [* *];
for p in Ps do
  X := MDX11(2, N, GF(p)); C := Curve(X);
  cusps := Cusps(X); fsFp := SigFunctions(X);
  classes := AssociativeArray();
  for c in cusps do sg := Signature(fsFp, c); if IsDefined(classes, sg) then Append(~classes[sg], c); else classes[sg] := [c]; end if; end for;
  assert #Keys(classes) eq r;
  orbits := [];
  for i in [1..r] do
    sg := Signature(fsQ, cuspsQ[i]); assert IsDefined(classes, sg);
    O := &+[Divisor(c) : c in classes[sg]]; assert Degree(O) eq Degree(cuspsQ[i]);
    Append(~orbits, O);
  end for;
  i0 := [i : i in [1..r] | Degree(orbits[i]) eq 1][1];
  c0 := Support(orbits[i0])[1];        // reduction of the Q-rational cusp cuspsQ[i0]
  Cl, m1, m2 := ClassGroup(C);
  Free := FreeAbelianGroup(r);
  h := hom< Free -> Cl | [m2(O - Degree(O)*Divisor(c0)) : O in orbits] >;
  G := Image(h);
  printf "PRIME %o: Cl(X_Fp) invariants %o, image of ClCusp_Q: %o, time %o\n", p, Invariants(Cl), Invariants(G), Cputime(t0);
  places := [Places(C, d) : d in [1..D]];
  printf "PRIME %o: places of degree 1..%o: %o\n", p, D, [#pl : pl in places];
  S := {}; cnt := 0;
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

p1, X1, h1, G1, S1, base1 := Explode(data[1]);
Free := Domain(h1); K := Kernel(h1);
Qgrp, qmap := quo< Free | K >;
printf "J(Q) = ClCusp_Q parametrised: order %o, invariants %o (compare DEHMZ Table 3)\n", #Qgrp, Invariants(Qgrp);
maps := [* *];
for dt in data do
  hp := dt[3];
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
printf "CANDIDATES_NONCUSPIDAL: %o candidate classes remain after removing the cuspidal classes (these are lifted to Q)\n", #noncusp;
printf "CANDIDATES: %o classes of J(Q) whose reduction is the class of an effective degree-%o divisor for all p in %o, time %o\n", #cands, D, Ps, Cputime(t0);

// short representatives of classes: reduce modulo the relation lattice K (full rank r) by CVP
Kbasis := Matrix(Integers(), [Eltseq(Free!k) : k in Generators(K)]);
Lat := LatticeWithBasis(LLL(Kbasis));
function ShortRep(vec)
  w := ClosestVector(Lat, Vector(Rationals(), vec));
  return [vec[i] - Integers()!w[i] : i in [1..#vec]];
end function;
c0Q := cuspsQ[[i : i in [1..r] | Degree(cuspsQ[i]) eq 1][1]];
nlift := 0; npoints := 0; ncusp := 0; nempty := 0; nbig := 0;
for c in noncusp do
  nlift +:= 1; if nlift mod 50 eq 0 then printf "LIFT progress %o/%o time %o\n", nlift, #noncusp, Cputime(t0); end if;
  v := ShortRep(Eltseq(c @@ qmap));
  gammaQ := &+[v[i]*Divisor(cuspsQ[i]) : i in [1..r]];
  gammaQ -:= Degree(gammaQ)*Divisor(c0Q);
  Dlift := D*Divisor(c0Q) + gammaQ;
  V, mV := RiemannRochSpace(Dlift);
  if Dimension(V) eq 0 then nempty +:= 1; continue; end if;
  if Dimension(V) ge 2 then
    nbig +:= 1;
    // a linear system of degree D and dimension >= 1: compute its fixed part; members are
    // (fixed part) + (moving part).  An irreducible degree-D point in the class would force the
    // fixed part to be 0 and give a degree-D function, which does not exist (Derickx-Sutherland).
    printf "PENCIL class %o: l = %o -- the class is a linear system; no irreducible degree-%o point in it\n", v, Dimension(V), D;
    continue;
  end if;
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
printf "RESULT X_1(2,%o) D=%o: %o candidate classes; %o false positives (no effective divisor), %o pencils, %o all-cuspidal effective divisors, %o effective divisors with a non-cuspidal component; time %o\n", N, D, #cands, nempty, nbig, ncusp, npoints, Cputime(t0);
print "DIRECT_DONE";
quit;
