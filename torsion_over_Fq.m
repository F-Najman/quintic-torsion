/* torsion_over_Fq.m -- for each n in Ns and prime p not dividing n, determine the set of k <= K
   such that some elliptic curve over F_{p^k} has a point of order n (equivalently, has a
   subgroup Z/n; for M=2 also test Z/2 x Z/n).  Brute force over j-invariants and all twists,
   so the result is unconditional.  Usage: magma -n -b Ns:=26,27 Ps:=2,3,5,7,11,13 K:=5 torsion_over_Fq.m */
SetColumns(0);
if not assigned Ns then Ns := [26]; elif Type(Ns) eq MonStgElt then Ns := [StringToInteger(s) : s in Split(Ns, ",")]; end if;
if not assigned Ps then Ps := [2,3,5,7,11,13]; elif Type(Ps) eq MonStgElt then Ps := [StringToInteger(s) : s in Split(Ps, ",")]; end if;
if not assigned K then K := 5; elif Type(K) eq MonStgElt then K := StringToInteger(K); end if;
// exponents (n2 of Z/n1 x Z/n2) of all elliptic curve groups over F_q, computed once per q
function GroupStructures(q)
  F := GF(q);
  res := {};
  for j in F do
    E := EllipticCurveFromjInvariant(j);
    for Et in Twists(E) do
      A := AbelianGroup(Et);
      inv := Invariants(A);   // [n1, n2] or [n2] or [] (trivial group)
      if #inv eq 0 then inv := [1]; end if;
      Include(~res, inv);
    end for;
  end for;
  return res;
end function;
cache := AssociativeArray();
for p in Ps do
  for k in [1..K] do
    q := p^k;
    if q gt 20000 then continue; end if;
    cache[q] := GroupStructures(q);
  end for;
end for;
for n in Ns do
  for p in Ps do
    if n mod p eq 0 then continue; end if;
    ks := []; ks2 := [];
    for k in [1..K] do
      q := p^k;
      if not IsDefined(cache, q) then continue; end if;
      S := cache[q];
      // point of order n exists iff n divides the exponent n2
      if exists{inv : inv in S | inv[#inv] mod n eq 0} then Append(~ks, k); end if;
      // Z/2 x Z/n subgroup: need n | n2 and 2 | n1 (n even) i.e. full 2-torsion and a point of order n
      if n mod 2 eq 0 and exists{inv : inv in S | #inv eq 2 and inv[2] mod n eq 0 and inv[1] mod 2 eq 0} then Append(~ks2, k); end if;
    end for;
    printf "TORSION n=%o p=%o : k with Z/%o over F_p^k = %o ; k with Z/2xZ/%o = %o\n", n, p, n, ks, n, ks2;
  end for;
end for;
print "DONE";
quit;
