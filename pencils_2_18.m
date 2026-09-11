/* pencils_2_18.m -- the 1926 cuspidal classes on X_1(2,18) that direct_analysis_X11.m does not
   lift to Q, and a computational proof that Q(X_1(2,18)) contains no function of degree exactly 5,
   independent of [DS, Proposition 5.4].

   Setup as in direct_analysis_X11.m: X = X_1(2,18) has rank 0 and J(Q) = ClCusp_Q [DEHMZ], and
   Galois orbits of cusps over F_5 are identified by cusp signatures (valuations of u, v, b, c,
   1-b-c, 4b^2+4bc-4b+c^2, x(kQ)) checked against the cuspidal closed points over Q.

   Argument.  Over F_5 a divisor class of degree 5 with h^0 = l contains (5^l-1)/4 effective
   divisors, so the exhaustive enumeration determines l; here l is 1 or 2 in every class that has
   an effective representative.  By semicontinuity, h^0 over Q of a class is at most h^0 over F_5
   of its reduction.  For the 1926 classes containing an effective rational cuspidal divisor:
     - if l = 1 over F_5 the class contains a single effective rational divisor, so no pencil;
     - if l = 2 over F_5 then h^0 over Q is at most 2, and the class contains at least two distinct
       effective rational cuspidal divisors, so h^0 over Q = 2 and the complete rational linear
       system is the pencil they span.  Its fixed part is the componentwise minimum of any two
       distinct members, hence of the cuspidal members, which the script computes.
   Exactly 27 classes are of the second kind, and in each of them the fixed part is a rational cusp,
   so the moving part has degree 4.  Every one of the 18 remaining (non-cuspidal) classes has l = 1.
   Hence no complete linear system of degree 5 on X_1(2,18) is base-point free, and there is no
   rational function of degree exactly 5.  Usage: magma -n -b pencils_2_18.m */
SetColumns(0);
SetQuitOnError(true);
N:=18; Ps:=[5]; D:=5; MemGB:=6;
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
  S := {}; cnt := 0; classcounts:=AssociativeArray();
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
    for g in partialcl do
      Include(~S,g); cnt+:=1;
      if IsDefined(classcounts,g) then classcounts[g]+:=1; else classcounts[g]:=1; end if;
    end for;
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
ncuspdiv := 0; cuspvectors:=AssociativeArray();
procedure AddCusp(vec, remaining, start, ~cuspclasses, ~ncuspdiv, ~cuspvectors)
  if remaining eq 0 then
    v := vec; v[i0] -:= D;
    cl:=qmap(Free!v);
    if IsDefined(cuspvectors,cl) then Append(~cuspvectors[cl],vec); else cuspvectors[cl]:=[vec]; end if;
    Include(~cuspclasses,cl); ncuspdiv+:=1; return;
  end if;
  for i in [start..r] do
    if degsQ[i] le remaining then
      v := vec; v[i] +:= 1;
      AddCusp(v, remaining - degsQ[i], i, ~cuspclasses, ~ncuspdiv, ~cuspvectors);
    end if;
  end for;
end procedure;
AddCusp([0 : i in [1..r]], D, 1, ~cuspclasses, ~ncuspdiv, ~cuspvectors);
printf "CUSPIDAL: %o effective rational cuspidal divisors of degree %o in %o distinct classes; all are candidates: %o\n", ncuspdiv, D, #cuspclasses, cuspclasses subset Seqset(cands);
noncusp := [c : c in cands | c notin cuspclasses];
printf "CANDIDATES_NONCUSPIDAL: %o candidate classes remain after removing the cuspidal classes (these are lifted to Q)\n", #noncusp;
printf "CANDIDATES: %o classes of J(Q) whose reduction is the class of an effective degree-%o divisor for all p in %o, time %o\n", #cands, D, Ps, Cputime(t0);


// The rational points of a complete linear system of section dimension l
// over F_5 number 1+5+...+5^(l-1). This determines l from the exhaustive list.
assert Seqset([classcounts[k]:k in Keys(classcounts)]) eq {1,6};
assert #cands eq 1944 and #cuspclasses eq 1926 and #noncusp eq 18;
npencils:=0;
for cl in cuspclasses do
    key:=maps[1](cl)+base1;
    if classcounts[key] eq 1 then continue; end if;
    assert classcounts[key] eq 6; // l over F_5 is exactly 2
    vecs:=cuspvectors[cl];
    assert #vecs ge 2; // distinct Q-rational effective divisors: l over Q >= 2
    assert #Seqset(vecs) eq #vecs;
    fixed:=[Min([v[i]:v in vecs]):i in [1..r]];
    fixeddegree:=&+[fixed[i]*degsQ[i]:i in [1..r]];
    assert fixeddegree eq 1;
    // Semicontinuity gives l over Q <= l over F_5 = 2. Thus these sections
    // span the Q-linear system, and their common rational cusp is fixed.
    npencils+:=1;
    printf "MOVING_CUSPIDAL_CLASS rational_cuspidal_members=%o finite_field_members=%o fixed_degree=%o
",#vecs,classcounts[key],fixeddegree;
end for;
assert &and[classcounts[maps[1](cl)+base1] eq 1:cl in noncusp];
printf "ALL_1944_CLASSES_CHECKED moving_classes=%o all_have_a_fixed_rational_cusp
",npencils;
print "NO_DEGREE_FIVE_RATIONAL_FUNCTION_INDEPENDENTLY_VERIFIED";
quit;
