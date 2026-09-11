/* verify_sporadic_curves.m
   Self-contained verification of the three sporadic quintic torsion groups
   Z/28, Z/30 and Z/2 x Z/18 (Theorem 1.1 of the paper).
   Run with:  magma -n -b verify_sporadic_curves.m
*/
SetColumns(0);
Qx<x> := PolynomialRing(Rationals());

print "======== 1. The curves with a point of order 28 and of order 30 ========";
/* Sutherland's coordinates on X_1(N): from a point (x0,y0) on the plane model one puts
     r = (x0^2*y0 - x0*y0 + y0 - 1)/(x0^2*y0 - x0),   s = (x0*y0 - y0 + 1)/(x0*y0),
     b = r*s*(r-1),  c = s*(r-1),
   and E = E(b,c): Y^2 + (1-c)XY - bY = X^3 - b X^2 has P = (0,0) of order N. */
data := [
  <28, x^5 - x^4 - 2*x^3 - x^2 + 2*x + 2, func<t | t^3 - 1>>,
  <30, x^5 + x^4 - 3*x^3 + 3*x + 1,       func<t | 2*t^4 + t^3 - 6*t^2 + 4*t + 4>>,
  <30, x^5 + x^4 - 7*x^3 + x^2 + 12*x + 3,func<t | (3*t^4 + 7*t^3 + 6*t^2 + 11*t - 73)/53>>
];
Es := [* *]; Ks := [* *];
for i in [1..#data] do
  N, f, yf := Explode(data[i]);
  K<al> := NumberField(f);  OK := MaximalOrder(K);
  x0 := al; y0 := yf(al);
  r := (x0^2*y0 - x0*y0 + y0 - 1)/(x0^2*y0 - x0);
  s := (x0*y0 - y0 + 1)/(x0*y0);
  b := r*s*(r-1);  c := s*(r-1);
  E := EllipticCurve([1-c, -b, -b, 0, 0]);  P := E![0,0];
  printf "\n--- N = %o, K = Q(al) with %o = 0 ---\n", N, f;
  /* check the values of b and c printed in the paper (equations (7.1), (7.2)) */
  if i eq 1 then
    bpap := 419*al^4 - 759*al^3 - 222*al^2 - 239*al + 1032;
    cpap := 17*al^4 - 31*al^3 - 8*al^2 - 11*al + 42;
  elif i eq 2 then
    bpap := -6378*al^4 - 1917*al^3 + 20475*al^2 - 14321*al - 9118;
    cpap := -114*al^4 - 34*al^3 + 366*al^2 - 257*al - 162;
  else
    bpap := 0; cpap := 0;   // the third point is checked below, over the field of the second
  end if;
  if i le 2 then
    printf "  (b,c) agree with the paper : %o\n", b eq bpap and c eq cpap;
    assert b eq bpap and c eq cpap;
  end if;
  printf "  disc(O_K)             : %o = %o\n", Discriminant(OK), Factorization(Discriminant(OK));
  printf "  signature, h, |Gal|   : %o, %o, %o\n", Signature(K), ClassNumber(K), #GaloisGroup(f);
  printf "  order of P = (0,0)    : %o   (expected %o)\n", Order(P), N;
  assert Order(P) eq N;
  T := TorsionSubgroup(E);
  printf "  E(K)_tors             : %o\n", Invariants(T);
  assert Invariants(T) eq [N];
  printf "  deg Q(j(E))           : %o ;  CM: %o\n", Degree(MinimalPolynomial(jInvariant(E))), HasComplexMultiplication(E);
  Em := MinimalModel(E);
  printf "  conductor norm        : %o = %o\n", Norm(Conductor(Em)), Factorization(Norm(Conductor(Em)));
  Append(~Es, E); Append(~Ks, K);
end for;
/* the two curves of level 30 live over the same field and are 2-isogenous over it */
K30 := Ks[2];  E2 := Es[2];
printf "\n  the two fields of level 30 are isomorphic: %o\n", IsIsomorphic(K30, Ks[3]);
rts := Roots(PolynomialRing(K30) ! (x^5 + x^4 - 7*x^3 + x^2 + 12*x + 3));
assert #rts ge 1;
be := rts[1][1];                                      // a root of the 2nd polynomial inside K30
y0 := (3*be^4 + 7*be^3 + 6*be^2 + 11*be - 73)/53;  x0 := be;
r := (x0^2*y0 - x0*y0 + y0 - 1)/(x0^2*y0 - x0);  s := (x0*y0 - y0 + 1)/(x0*y0);
bb := r*s*(r-1);  cc := s*(r-1);
/* check the values printed in the paper (equation (7.3)) */
bpap := 190*be0^4 - 38*be0^3 - 382*be0^2 + 238*be0 + 295 where be0 := K30.1;
cpap := 7*be0^4 + 13*be0^3 - 36*be0^2 + 9*be0 + 28 where be0 := K30.1;
printf "  (b,c) of the second level-30 point agree with the paper: %o\n", bb eq bpap and cc eq cpap;
assert bb eq bpap and cc eq cpap;
E3 := EllipticCurve([1-cc, -bb, -bb, 0, 0]);
printf "  second curve realised over the same field, torsion %o, P of order %o\n",
       Invariants(TorsionSubgroup(E3)), Order(E3![0,0]);
printf "  E2 and E3 are K-isomorphic               : %o\n", IsIsomorphic(E2, E3);
Kx<X> := PolynomialRing(K30);
G2, m2 := TwoTorsionSubgroup(E2);
found := false;
for g in G2 do
  if g eq G2!0 then continue; end if;
  T2 := m2(g);
  Ei := IsogenyFromKernel(E2, X - T2[1]);
  if IsIsomorphic(Ei, E3) then found := true; end if;
end for;
printf "  E2 and E3 are 2-isogenous over K         : %o\n", found;
assert found;

print "";
print "======== 2. The curve with torsion Z/2 x Z/18 ========";
/* Derickx-Sutherland coordinates on X_1(2,2n): E : Y^2 = X^3 + c X^2 + (1-b-c) b X
   with P = (0,0) of order 2 and Q = (b,b) of order 2n. */
g := x^5 - 2*x^4 + 2*x^3 - 3*x^2 - x + 4;            // LMFDB field 5.3.34779.1
K<w> := NumberField(g);  OK := MaximalOrder(K);
/* equation (7.4) of the paper */
b := (480*w^4 - 1364*w^3 + 2108*w^2 - 3216*w + 2248)/3;
c := (-940*w^4 + 2668*w^3 - 4128*w^2 + 6296*w - 4389)/3;
E := EllipticCurve([0, c, 0, (1-b-c)*b, 0]);
P := E![0,0];  Q := E![b,b];
printf "  defining polynomial   : %o\n", g;
printf "  disc(O_K)             : %o = %o\n", Discriminant(OK), Factorization(Discriminant(OK));
printf "  signature, h, |Gal|   : %o, %o, %o\n", Signature(K), ClassNumber(K), #GaloisGroup(g);
printf "  order of P, order of Q: %o, %o\n", Order(P), Order(Q);
assert Order(P) eq 2 and Order(Q) eq 18;
T := TorsionSubgroup(E);
printf "  E(K)_tors             : %o\n", Invariants(T);
assert Invariants(T) eq [2,18];
printf "  deg Q(j(E))           : %o ;  CM: %o\n", Degree(MinimalPolynomial(jInvariant(E))), HasComplexMultiplication(E);
printf "  j(E)                  : %o\n", jInvariant(E);
printf "  min poly of j(E)      : %o\n", MinimalPolynomial(jInvariant(E));
Em := MinimalModel(E);
printf "  conductor norm        : %o = %o\n", Norm(Conductor(Em)), Factorization(Norm(Conductor(Em)));
printf "  a-invariants of a global minimal model: %o\n", aInvariants(Em);
/* the three 2-isogenous curves: needed to rule out Z/36 */
Kx<X> := PolynomialRing(K);
G2, m2 := TwoTorsionSubgroup(E);
for g2 in G2 do
  if g2 eq G2!0 then continue; end if;
  T2 := m2(g2);
  Ei := IsogenyFromKernel(E, X - T2[1]);
  inv := Invariants(TorsionSubgroup(Ei));
  printf "  E/<(%o,0)> has torsion %o ; a point of order 36? %o\n", T2[1], inv,
         exists{i : i in inv | i mod 36 eq 0};
  assert not exists{i : i in inv | i mod 36 eq 0};
end for;
print "";
print "ALL CHECKS PASSED";
quit;
