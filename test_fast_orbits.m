SetColumns(0);
AttachSpec("mdmagma/v2/mdmagma.spec");
Attach("fast_hecke.m");
for NPd in [<26,7,[2,3,4]>, <28,5,[2,3,4,5]>, <28,3,[3,4,5]>, <33,7,[3,4]>, <30,7,[2,3,4]>] do
  N, p, degs := Explode(NPd);
  X := MDX1(N, GF(p));
  for d in degs do
    S := NoncuspidalPlaces(X, d);
    t := Cputime(); fr := PlacesUpToDiamondFast(X, S); tf := Cputime(t);
    t := Cputime(); orbits := [Seqset(DiamondOrbit(X, r)) : r in fr]; torb := Cputime(t);
    disjoint := &and[ #(orbits[i] meet orbits[j]) eq 0 : i, j in [1..#orbits] | i lt j ];
    cover := &join orbits eq Seqset(S);
    t := Cputime(); sr := PlacesUpToDiamond(X, S); ts := Cputime(t);
    printf "TESTORB N=%o p=%o deg %o: %o places, fast reps %o (%o s), mdmagma reps %o (%o s), orbits disjoint %o, cover %o\n", N, p, d, #S, #fr, tf, #sr, ts, disjoint, cover; _ := torb;
    assert disjoint and cover and #fr eq #sr;
  end for;
end for;
print "TESTORB_DONE";
quit;
