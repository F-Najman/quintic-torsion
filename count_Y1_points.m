/* count_Y1_points.m -- independent verification of the place counts used by the sieve.
   For each pair (N,p) [and (2,2n),p] and each d <= 5 we count
        #Y_1(m,n)(F_{p^d})  =  #{ (E,P[,Q])/F_{p^d} } / iso
   by brute force over all elliptic curves over F_{p^d} (all j, all twists, orbits of the
   points under Aut(E)).  Since X_1(m,n) is a fine moduli space for mn > 4, this must equal
        sum_{e | d}  e * #{ non-cuspidal places of X_1(m,n)/F_p of degree e }.
   The right-hand side is read off from the sieve logs (NONCUSP lines); the left-hand side
   is computed here and is completely independent of any model of the modular curve.
   Usage: magma -n -b N:=45 p:=7 M:=1 count_Y1_points.m          (M=2 means X_1(2,N)) */
SetColumns(0);
if not assigned N then N := 45; elif Type(N) eq MonStgElt then N := StringToInteger(N); end if;
if not assigned p then p := 7; elif Type(p) eq MonStgElt then p := StringToInteger(p); end if;
if not assigned M then M := 1; elif Type(M) eq MonStgElt then M := StringToInteger(M); end if;
if not assigned D then D := 5; elif Type(D) eq MonStgElt then D := StringToInteger(D); end if;
// Magma's Twists handles all characteristics, including p = 2, 3.

function CountPairs(F, N, M)
  // number of isomorphism classes of (E,P) [M=1] or (E,P2,Q) [M=2] over F
  total := 0;
  for j in F do
    E0 := EllipticCurveFromjInvariant(j);
    for E in Twists(E0) do
      A, mA := AbelianGroup(E);
      inv := Invariants(A);
      if M eq 1 then
        if not exists{i : i in inv | i mod N eq 0} then continue; end if;
        S := {mA(g) : g in A | Order(g) eq N};
      else
        // triples (E,P,Q): P of order 2, Q of order N, <P,Q> = Z/2 x Z/N  (N even)
        if #inv lt 2 or (inv[#inv] mod N ne 0) or (inv[1] mod 2 ne 0) then continue; end if;
        S := {};
        Qs := [mA(g) : g in A | Order(g) eq N];
        Ps := [mA(g) : g in A | Order(g) eq 2];
        for QQ in Qs do
          for PP in Ps do
            if PP ne (N div 2)*QQ then Include(~S, <PP, QQ>); end if;
          end for;
        end for;
      end if;
      if #S eq 0 then continue; end if;
      auts := Automorphisms(E);
      // count orbits of Aut(E) on S
      seen := {};  norb := 0;
      for s in S do
        if s in seen then continue; end if;
        norb +:= 1;
        for a in auts do
          if M eq 1 then Include(~seen, a(s)); else Include(~seen, <a(s[1]), a(s[2])>); end if;
        end for;
      end for;
      total +:= norb;
    end for;
  end for;
  return total;
end function;

lev := N;   // for M = 2 the parameter N is the full level 2n of X_1(2,2n)
printf "COUNT curve=X_1(%o,%o) p=%o\n", M, lev, p;
t0 := Cputime();
for d in [1..D] do
  F := GF(p^d);
  c := CountPairs(F, lev, M);
  printf "YCOUNT d=%o  #Y(F_{%o^%o}) = %o   time=%o\n", d, p, d, c, Cputime(t0);
end for;
print "COUNT_DONE";
quit;
