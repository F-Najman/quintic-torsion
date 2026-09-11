SetColumns(0);
AttachSpec("mdmagma/v2/mdmagma.spec");
Attach("fast_hecke.m");
t0 := Cputime();
// correctness: compare with mdmagma's HeckeOperator on many places
for NP in [<26,7>, <28,5>, <30,7>] do
  N, p := Explode(NP);
  X := MDX1(N, GF(p));
  for d in [2,3,4] do
    pl := NoncuspidalPlaces(X, d); pl := pl[1..Min(#pl, 12)];
    for q in [qq : qq in [3,5,11,13] | qq ne p and N mod qq ne 0][1..2] do
      nok := 0; tf := 0; ts := 0;
      for x in pl do
        t := Cputime(); Df := HeckeOperatorFast(X, q, x); tf +:= Cputime(t);
        t := Cputime(); Ds := HeckeOperator(X, q, x); ts +:= Cputime(t);
        if Df eq Ds then nok +:= 1; else printf "TESTFAST MISMATCH N=%o p=%o d=%o q=%o place %o\n", N, p, d, q, x; end if;
      end for;
      printf "TESTFAST N=%o p=%o deg %o q=%o: %o/%o agree; fast %o s, mdmagma %o s\n", N, p, d, q, nok, #pl, tf, ts;
      assert nok eq #pl;
    end for;
  end for;
end for;
// speed on the slow case found by diag45: X_1(45)/F_7, degree-5 place number 50, q = 11
X := MDX1(45, GF(7)); P5 := NoncuspidalPlaces(X, 5);
for i in [1, 50] do
  t := Cputime(); Df := HeckeOperatorFast(X, 11, P5[i]); printf "TESTFAST X1(45)/F7 place %o: T_11 fast %o s (degree %o)\n", i, Cputime(t), Degree(Df);
end for;
t := Cputime(); Ds := HeckeOperator(X, 11, P5[1]); ts := Cputime(t);
agrees := Ds eq HeckeOperatorFast(X, 11, P5[1]);
printf "TESTFAST X1(45)/F7 place 1: T_11 mdmagma %o s, agree=%o\n", ts, agrees;
assert agrees;
printf "TESTFAST_DONE %o\n", Cputime(t0);
quit;
