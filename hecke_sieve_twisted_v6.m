/* hecke_sieve_twisted.m -- POSITIVE RANK variant (method M6 of notes/01): the operator
   t_{a,q} := A_q(<a>D) - A_q(D) kills J(Q) whenever (<a>-1)J(Q) is finite (a in the kernel of all
   characters of positive-rank newforms).  A divisor D survives only if [t_{a,q} D] = 0 for ALL a in As
   and all admissible q.  Divisors fixed by every <a> in As survive trivially and must be treated by hand.
   Otherwise identical to hecke_sieve_deg5.m (v5).
/* v6: uses HeckeOperatorFast / PlacesUpToDiamondFast from fast_hecke.m (validated in logs/test_fast_hecke.log, logs/test_fast_orbits.log).
/* hecke_sieve_deg5.m (v3) -- degree-D Hecke sieve on X_1(N) (M=1) or X_1(2,N) (M=2) over F_p.
   Implements Prop. 5.5 / Cor. 5.6 of Derickx-Najman (arXiv:2412.16016) for arbitrary degree D,
   with the congruence condition on q for the cuspidal complement computed rigorously from the
   fields of definition of the cusps (notes/01_methods.md, method M2, refined form):
   for a non-cuspidal part D' of degree d' < D the cuspidal complement C has degree k = D-d',
   and [A_q C] = 0 is guaranteed if q lies in <p>.H_c for every Galois orbit c of cusps whose
   F_p-reduction has degree <= k, where H_c = Gal(Q(zeta_N)/F_c) and F_c = field of definition
   (residue field of the cuspidal closed point on the model over Q, embedded in Q(zeta_N)).
   Hypotheses verified elsewhere: rk J(Q) = 0; the all-cuspidal reduction excluded by Prop 5.1.
   Usage: magma -n -b N:=26 p:=7 Qs:=3,5,11,13 D:=5 M:=1 MemGB:=8 hecke_sieve_deg5.m
   Log markers: SETUP CUSPS CUSPFIELDS CC NONCUSP REPS QLIST TYPE PROGRESS SURVIVOR SURVIVOR_DATA
                RESULT SUMMARY SIEVE_DONE ERROR */
SetColumns(0);
if not assigned N then N := 26; elif Type(N) eq MonStgElt then N := StringToInteger(N); end if;
if not assigned p then p := 7; elif Type(p) eq MonStgElt then p := StringToInteger(p); end if;
if not assigned D then D := 5; elif Type(D) eq MonStgElt then D := StringToInteger(D); end if;
if not assigned M then M := 1; elif Type(M) eq MonStgElt then M := StringToInteger(M); end if;
if not assigned Qs then Qs := [3,5,7,11,13]; elif Type(Qs) eq MonStgElt then Qs := [StringToInteger(s) : s in Split(Qs, ",")]; end if;
if not assigned Hs then Hs := []; elif Type(Hs) eq MonStgElt then Hs := [StringToInteger(t) : t in Split(Hs, ",")]; end if;   // H-variant: operator A_q(D + <h>D), valid when J(X/<±h>)(Q) is finite
if not assigned SkipCusps then SkipCusps := 0; elif Type(SkipCusps) eq MonStgElt then SkipCusps := StringToInteger(SkipCusps); end if;
if not assigned As then As := [2,3]; elif Type(As) eq MonStgElt then As := [StringToInteger(t) : t in Split(As, ",")]; end if;
if not assigned MemGB then MemGB := 8; elif Type(MemGB) eq MonStgElt then MemGB := StringToInteger(MemGB); end if;
if not assigned Shard then Shard := 0; elif Type(Shard) eq MonStgElt then Shard := StringToInteger(Shard); end if;
if not assigned NShard then NShard := 1; elif Type(NShard) eq MonStgElt then NShard := StringToInteger(NShard); end if;
SetMemoryLimit(MemGB*10^9);
AttachSpec("mdmagma/v2/mdmagma.spec");
Attach("fast_hecke.m");   // v6: fast Hecke operators and diamond orbits (X_1(N) only)
function HeckeOp(X, q, D) if M eq 1 then return HeckeOperatorFast(X, q, D); else return HeckeOperator(X, q, D); end if; end function;
function PUD(X, S) if #S eq 0 then return S; elif M eq 1 then return PlacesUpToDiamondFast(X, S); else return PlacesUpToDiamond(X, S); end if; end function;
t0 := Cputime();
if M eq 1 then X := MDX1(N, GF(p)); else X := MDX11(2, N, GF(p)); end if;
printf "SETUP N=%o M=%o p=%o genus=%o time=%o\n", N, M, p, Genus(X), Cputime(t0);
if SkipCusps eq 1 then cusps := []; print "CUSPS skipped (SkipCusps=1): the cusp structure below comes from DEHMZ Lemma 2.7 only";
else cusps := Cusps(X); printf "CUSPS number=%o degrees=%o\n", #cusps, Sort([Degree(c) : c in cusps]); end if;

// ---- fields of definition of the cusps ----
// M=1: DEHMZ (arXiv:2007.13929) Lemma 2.7: the cuspidal subscheme of X_1(N) over Z[1/2N] is
//   the disjoint union over d | N of (mu_{N/d} x Z/d)'/[-1]; Galois acts on mu_{N/d} only, so a cusp
//   of type d has stabiliser H = {k = 1 mod N/d} (d > 2) or {k = +-1 mod N/d} (d <= 2) in (Z/N)^*.
// M=2: computed from the model over Q (residue fields of the cuspidal closed points).
Cyc<z> := CyclotomicField(N);
ZN := Integers(N);
units := [a : a in [1..N] | GCD(a, N) eq 1];
cuspdata := [* *];
if M eq 1 then
  for d in Divisors(N) do
    m := N div d;
    if d gt 2 then H := { a : a in units | a mod m eq 1 mod m }; else H := { a : a in units | (a mod m) in {1 mod m, (m-1) mod m} }; end if;
    // number of cusps of type d: phi(d)*phi(N/d)/2 (d>2 or ...); orbits have size #units/#H
    ncusps_d := (EulerPhi(d)*EulerPhi(m)) div 2;
    if d le 2 and m le 2 then ncusps_d := 1; end if;     // N in {1,2,4}: not our case
    orbsize := #units div #H;
    assert ncusps_d mod orbsize eq 0;
    for i in [1..(ncusps_d div orbsize)] do Append(~cuspdata, <orbsize, H>); end for;
  end for;
else
  XQ := MDX11(2, N, Rationals());
  cuspsQ := Cusps(XQ);
  for c in cuspsQ do
    dc := Degree(c);
    if dc eq 1 then H := Seqset(units);
    else
      Fabs := AbsoluteField(NumberField(ResidueClassField(c)));
      ok, emb := IsSubfield(Fabs, Cyc);
      if not ok then error "cusp field is not a subfield of Q(zeta_N)"; end if;
      g := emb(Fabs.1);
      H := { a : a in units | Evaluate(Polynomial(Eltseq(g)), z^a) eq g };
      assert #units div #H eq dc;
    end if;
    Append(~cuspdata, <dc, H>);
  end for;
end if;
if SkipCusps eq 0 then assert &+[d[1] : d in cuspdata] eq &+[Degree(c) : c in cusps]; end if;   // same number of geometric cusps
Hp := {ZN!1}; hh := ZN!p; while hh notin Hp do Include(~Hp, hh); hh *:= p; end while;
fdeg := [];
for d in cuspdata do
  f := 1; x := ZN!p; while (Integers()!x) notin d[2] do x *:= p; f +:= 1; end while; Append(~fdeg, f);
end for;
// consistency: multiset of F_p-degrees of cusps computed on X_{F_p} equals predicted from fields
predicted := {* fdeg[i]^^(cuspdata[i][1] div fdeg[i]) : i in [1..#cuspdata] *};
actual := {* Degree(c) : c in cusps *};
printf "CUSPFIELDS orbits over Q (degree, F_p-degree): %o ; predicted F_p cusp degrees match model: %o\n", [<cuspdata[i][1], fdeg[i]> : i in [1..#cuspdata]], SkipCusps eq 1 select "not checked" else predicted eq actual;
if SkipCusps eq 0 then assert predicted eq actual; end if;
Qs := [q : q in Qs | IsPrime(q) and q ne p and (2*N) mod q ne 0];
QsCC := [];   // QsCC[k] = admissible q for cuspidal complement of degree <= k
for k in [1..D-1] do
  adm := Seqset(units);
  for i in [1..#cuspdata] do
    if fdeg[i] le k then adm meet:= { Integers()!(a*b) : a in Hp, b in cuspdata[i][2] }; end if;
  end for;
  Append(~QsCC, [q : q in Qs | (q mod N) in adm]);
  printf "CC complement degree <= %o: q mod %o in %o ; usable q from list: %o\n", k, N, Sort(Setseq(adm)), QsCC[k];
end for;
printf "QLIST all (used when there is no cuspidal part): %o ; twist diamonds As=%o ; H-sums Hs=%o\n", Qs, As, Hs;

// Which degrees d can carry non-cuspidal places?  A non-cuspidal place of degree d gives an
// elliptic curve over F_{p^d} with a point of order N (M=1) or a subgroup Z/2 x Z/N (M=2).
// Enumerate all E/F_{p^d} (all j, all twists) -- unconditional -- and skip empty degrees.
function DegreeHasPoints(d)
  F := GF(p^d);
  for j in F do
    E := EllipticCurveFromjInvariant(j);
    for Et in Twists(E) do
      inv := Invariants(AbelianGroup(Et)); if #inv eq 0 then inv := [1]; end if;
      if M eq 1 then
        if inv[#inv] mod N eq 0 then return true; end if;
      else
        if #inv eq 2 and inv[2] mod N eq 0 and inv[1] mod 2 eq 0 then return true; end if;
      end if;
    end for;
  end for;
  return false;
end function;
hasdeg := [ (p^d le 400000) select DegreeHasPoints(d) else true : d in [1..D] ];
printf "DEGREES with points of the required type over F_p^d (d=1..%o): %o  time=%o\n", D, hasdeg, Cputime(t0);
places := [ hasdeg[d] select NoncuspidalPlaces(X, d) else [] : d in [1..D] ];
printf "NONCUSP counts deg 1..%o: %o  time=%o\n", D, [#places[d] : d in [1..D]], Cputime(t0);
reps := [ PUD(X, places[d]) : d in [1..D] ];
printf "REPS up to diamond: %o  time=%o\n", [#reps[d] : d in [1..D]], Cputime(t0);

function DivisorsOfType(lambda)
  d1 := lambda[1]; rest := lambda[2..#lambda];
  degs := Sort(Setseq(Seqset(rest)));
  result := [];
  for e in degs do if #places[e] eq 0 then return result; end if; end for;
  if #reps[d1] eq 0 then return result; end if;
  choices := [* *];
  for e in degs do
    k := #[x : x in rest | x eq e];
    Append(~choices, [ &+[Divisor(x) : x in S] : S in Multisets(Seqset(places[e]), k) ]);
  end for;
  for R in reps[d1] do
    partial := [Divisor(R)];
    for ch in choices do partial := [ a + b : a in partial, b in ch ]; end for;
    result cat:= partial;
  end for;
  return result;
end function;

function Describe(Dv)
  a, b := Support(Dv);
  return [< b[i], Degree(a[i]), jInvariant(X, a[i]) > : i in [1..#a]];
end function;
// reconstructible description of a divisor: for each place [* deg, mult, defpoly, coords *]
// where defpoly is the defining polynomial (coefficient list over F_p) of the field K of a
// representative point and coords the Eltseq's of its projective coordinates in K;
// reconstruct with K := ext<GF(p)|Polynomial(GF(p),defpoly)>; Places(Curve(X)(K)![K!c : c in coords]).
function DescribeData(Dv)
  a, b := Support(Dv);
  out := [* *];
  for i in [1..#a] do
    P := a[i]; dg := Degree(P);
    try
      pt := RepresentativePoint(P);
      K := Ring(Parent(pt));
      defpoly := [Integers()!c : c in Eltseq(DefiningPolynomial(K, GF(p)))];
      coords := [[Integers()!e : e in Eltseq(c, GF(p))] : c in Eltseq(pt)];
      Append(~out, [* dg, b[i], defpoly, coords *]);
    catch e
      Append(~out, [* dg, b[i], "ERROR", Sprint(e`Object) *]);
    end try;
  end for;
  return out;
end function;

allsurv := [];
for dd in [1..D] do
  qlist := (dd eq D) select Qs else QsCC[D-dd];
  for lambda in Partitions(dd) do
    divs := DivisorsOfType(lambda);
    if #divs eq 0 then printf "TYPE %o: no divisors\n", lambda; continue; end if;
    if NShard gt 1 then divs := [divs[i] : i in [1..#divs] | (i mod NShard) eq Shard]; end if;
    printf "TYPE %o: %o divisors (up to diamond%o), qlist=%o\n", lambda, #divs, NShard gt 1 select Sprintf(", shard %o of %o", Shard, NShard) else "", qlist;
    if #qlist eq 0 then printf "ERROR type=%o: no admissible q -- all %o divisors count as survivors\n", lambda, #divs; end if;
    surv := 0; cnt := 0;
    for Dv in divs do
      cnt +:= 1; killed := false; err := false;
      for q in qlist do
        try
          AqD := HeckeOp(X, q, Dv) - q*DiamondOperator(X, q, Dv) - Dv;
          for a in As do
            Da := DiamondOperator(X, a, Dv);
            if Da eq Dv then continue; end if;      // fixed by <a>: this a gives no information
            tD := HeckeOp(X, q, Da) - q*DiamondOperator(X, q, Da) - Da - AqD;
            if not IsPrincipal(tD) then killed := true; break; end if;
          end for;
          if not killed then
            for h in Hs do
              Dh := DiamondOperator(X, h, Dv);
              tD := HeckeOp(X, q, Dh) - q*DiamondOperator(X, q, Dh) - Dh + AqD;   // A_q(D + <h>D)
              if not IsPrincipal(tD) then killed := true; break; end if;
            end for;
          end if;
          if killed then break; end if;
        catch e
          err := true; printf "ERROR type=%o q=%o divisor=%o msg=%o\n", lambda, q, Describe(Dv), e`Object;
        end try;
      end for;
      if not killed then
        surv +:= 1; Append(~allsurv, <lambda, Dv>);
        try printf "SURVIVOR type=%o err=%o divisor=%o\n", lambda, err, Describe(Dv); catch e printf "SURVIVOR type=%o err=%o divisor=(describe failed)\n", lambda, err; end try;
        printf "SURVIVOR_DATA type=%o data=%o\n", lambda, DescribeData(Dv);
      end if;
      if cnt mod 100 eq 0 then printf "PROGRESS type=%o %o/%o survivors=%o time=%o\n", lambda, cnt, #divs, surv, Cputime(t0); end if;
    end for;
    printf "RESULT type=%o total=%o survivors=%o time=%o\n", lambda, #divs, surv, Cputime(t0);
  end for;
end for;
printf "SUMMARY N=%o M=%o p=%o D=%o shard=%o/%o total_survivors=%o time=%o\n", N, M, p, D, Shard, NShard, #allsurv, Cputime(t0);
print "SIEVE_DONE";
quit;
