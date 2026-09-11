SetColumns(0);
AttachSpec("mdmagma/v2/mdmagma.spec");
for NP in [<26,7>,<26,11>,<28,3>,<28,5>,<30,7>,<30,11>,<30,13>] do
  N, p := Explode(NP);
  X := MDX1(N, GF(p)); C := Curve(X);
  cusps := Cusps(X); orbits := [Type(O) eq PlcCrvElt select Divisor(O) else O : O in CuspOrbitsQ(X)];   // uniform divisor type
  Cl, m1, m2 := ClassGroup(C);
  c0 := [c : c in cusps | Degree(c) eq 1][1];
  GQ := sub<Cl | [m2(O - Degree(O)*Divisor(c0)) : O in orbits]>;
  Gall := sub<Cl | [m2(Divisor(c) - Degree(c)*Divisor(c0)) : c in cusps]>;
  tors := [i : i in Invariants(Cl) | i ne 0];
  printf "N=%o p=%o: #cusps %o (degrees %o), orbit degrees %o, J(F_p)_tors=%o (order %o), <Q-orbit sums>=%o (order %o), <all F_p cusps>=%o (order %o)\n",
    N, p, #cusps, Sort([Degree(c) : c in cusps]), Sort([Degree(O) : O in orbits]), tors, &*tors, Invariants(GQ), #GQ, Invariants(Gall), #Gall;
end for;
print "CUSPGROUP_DONE";
quit;
