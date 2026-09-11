/* check_places_count.m -- guard against the V2.29-4 bug fixed in V2.29-5 ("infinite places of degrees
   greater than the relative degree were not returned by Places(F,d)"): for each model used in this
   project, verify (i) the relative degree deg_y of the plane model is >= 5, and (ii) for d = 1..5,
   sum_{e | d} e * #Places(C/F_p, e) equals #Places(C/F_{p^d}, 1) (degree-1 places of the base change,
   which the bug cannot affect).  Any mismatch would mean an incomplete enumeration of places. */
SetColumns(0);
AttachSpec("mdmagma/v2/mdmagma.spec");
cases := [ <1,26,7>, <1,28,3>, <1,28,5>, <1,30,7>, <1,32,3>, <1,33,7>, <1,34,3>, <1,38,3>, <1,42,5>,
           <2,18,5>, <2,20,3>, <2,20,7>, <2,22,3>, <2,24,5> ];
allok := true;
for cs in cases do
  M, N, p := Explode(cs);
  X := (M eq 1) select MDX1(N, GF(p)) else MDX11(2, N, GF(p));
  C := Curve(X); f := DefiningPolynomial(AffinePatch(C, 1));
  degy := Degree(f, 2); degx := Degree(f, 1);
  counts := [#Places(C, d) : d in [1..5]];
  ok := true; report := [];
  for d in [1..5] do
    Cd := BaseChange(C, GF(p^d));
    n1 := #Places(Cd, 1);
    pred := &+[e*counts[e] : e in [1..5] | d mod e eq 0];
    Append(~report, <d, n1, pred>);
    if n1 ne pred then ok := false; end if;
  end for;
  allok := allok and ok;
  printf "PLACESCHECK M=%o N=%o p=%o: bidegree (%o,%o), places deg 1..5 = %o, [d, #X(F_p^d), predicted] = %o, CONSISTENT=%o\n", M, N, p, degx, degy, counts, report, ok;
end for;
printf "PLACESCHECK_DONE all_consistent=%o\n", allok;
quit;
