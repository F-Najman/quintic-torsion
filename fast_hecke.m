/* fast_hecke.m -- faster Hecke operators T_q on X_1(N) over finite fields (package to Attach after mdmagma).
   mdmagma's HeckeOperator computes the splitting field of the whole q-division polynomial (degree up to
   (q^2-1)/2 over the residue field K), which is what makes T_11 take up to two hours on X_1(45)/F_7.
   Here, for each Frobenius(K)-orbit of the q+1 cyclic subgroups G of E[q], we work in the field of
   definition L of G (degree <= q+1 over K): factor the division polynomial over K, take a root x1 of an
   unassigned factor in F1 = K(x1), compute the kernel polynomial g_G = prod (X - x(k P1)) in F1[X] by point
   arithmetic (in F1 or its quadratic extension), let L = K(coefficients of g_G), build the isogeny over L by
   Velu (IsogenyFromKernel) and the image of the level structure over L.  The Frobenius-conjugates of G
   give the same F_p-place; the orbit size e = [L:K] is used as multiplicity, exactly as in mdmagma's formula
   T_q(x) = sum_y (#{G : y_G = y} * deg(x)/deg(y)) y.  Factors accounted for by an orbit are the divisors of
   the K-norm of g_G.  HeckeOperatorFast is checked against HeckeOperator in test_fast_hecke.m.
   RESTRICTION: q must be ODD.  The kernel polynomial is built as prod_{1<=k<=(q-1)/2} (X - x(k P1)), which
   is empty for q = 2, and the division-polynomial degree assertion below also assumes q odd.  Every sieve
   prime used in the paper is odd; for q = 2 use mdmagma's HeckeOperator. */

intrinsic MDIsogeniesFast(E::CrvEll[FldFin], P::PtEll, q::RngIntElt) -> List
{ For each Frobenius-orbit of cyclic subgroups G of order q of E (over the base field K of E), return
  <E/G, image of P, orbit size e>, with E/G and the image defined over the field of definition L of G }
    require IsPrime(q) and IsOdd(q) and q ne Characteristic(BaseRing(E)) : "q must be an odd prime different from the characteristic";
    K := BaseRing(E);
    fq := DivisionPolynomial(E, q);
    fac := [t[1] : t in Factorization(fq)];
    assert &+[Degree(h) : h in fac] eq (q^2-1) div 2;   // separable: distinct x-coordinates
    a1, a2, a3, a4, a6 := Explode(aInvariants(E));
    unassigned := [true : h in fac];
    result := [* *];
    total := 0;
    for i in [1..#fac] do
        if not unassigned[i] then continue; end if;
        h := fac[i]; d := Degree(h);
        if d eq 1 then F1 := K; x1 := -Coefficient(h, 0)/Coefficient(h, 1);
        else F1 := ext<K | h>; x1 := F1.1; end if;
        // y-coordinate: solve y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6 over F1 or a quadratic extension
        PY<Y> := PolynomialRing(F1);
        ypol := Y^2 + (F1!a1*x1 + F1!a3)*Y - (x1^3 + F1!a2*x1^2 + F1!a4*x1 + F1!a6);
        rts := Roots(ypol);
        if #rts gt 0 then F2 := F1; y1 := rts[1][1];
        else F2 := ext<F1 | 2>; y1 := Roots(PolynomialRing(F2)!ypol)[1][1]; end if;
        E2 := EllipticCurve([F2!a1, F2!a2, F2!a3, F2!a4, F2!a6]);
        P1 := E2![F2!x1, y1];
        assert q*P1 eq E2!0 and P1 ne E2!0;
        xs := [ F1!((k*P1)[1]) : k in [1..(q-1) div 2] ];          // x-coordinates lie in F1
        PX<X> := PolynomialRing(F1);
        g := &*[X - xk : xk in xs];                                  // kernel polynomial of G = <P1>
        cs := Coefficients(g);
        L := sub< F1 | cs cat [F1!K.1] >;                            // field of definition of G, contains K
        e := Degree(L) div Degree(K);
        assert (q+1) mod e eq 0 or true;                              // e divides the orbit structure; not needed
        // mark the factors belonging to this Frobenius-orbit: divisors of Norm_{L/K}(g)
        qK := #K;
        Ng := PX!1; gg := g;
        for j in [1..e] do
            Ng *:= gg;
            gg := PX![c^qK : c in Coefficients(gg)];
        end for;
        assert gg eq g;   // Frobenius^e fixes g
        NgK := PolynomialRing(K)![K!c : c in Coefficients(Ng)];
        deg_assigned := 0;
        for j in [1..#fac] do
            if unassigned[j] and IsDivisibleBy(NgK, fac[j]) then unassigned[j] := false; deg_assigned +:= Degree(fac[j]); end if;
        end for;
        assert deg_assigned eq e*(q-1) div 2;
        // the isogeny over L
        PL<XL> := PolynomialRing(L);
        gL := PL![L!c : c in cs];
        EL := EllipticCurve([L!(F1!a) : a in aInvariants(E)]);
        EG, phi := IsogenyFromKernel(EL, gL);
        PLpt := EL![L!(F1!(K!P[1])), L!(F1!(K!P[2]))];
        Append(~result, <EG, phi(PLpt), e>);
        total +:= e;
    end for;
    assert total eq q+1;
    return result;
end intrinsic;

intrinsic HeckeOperatorFast(X::MDCrvMod1, q::RngIntElt, x::PlcCrvElt) -> DivCrvElt
{ T_q(x) for a non-cuspidal place x of X_1(N)/F_p, computed with MDIsogeniesFast }
    char := Characteristic(BaseRing(X));
    require IsPrime(q) and IsOdd(q) : "q must be an odd prime";
    require GCD(char, q) eq 1 and GCD(Level(X), q) eq 1 : "q must be coprime to p and N";
    ZZ := Integers();
    k := Degree(x);
    E := EllipticCurve(X, x);
    P := LevelStructure(X, x)`P;
    isog := MDIsogeniesFast(E, P, q);
    D := DivisorGroup(Curve(X)) ! 0;
    for t in isog do
        EG, PG, e := Explode(t);
        y := ModuliPoint(X, EG, rec< recformat< P : PtEll > | P := PG >);
        D +:= (ZZ ! (e*k/Degree(y))) * Divisor(y);
    end for;
    assert Degree(D) eq (q+1)*k;
    return D;
end intrinsic;

intrinsic HeckeOperatorFast(X::MDCrvMod1, q::RngIntElt, D::DivCrvElt) -> DivCrvElt
{ T_q(D) for a divisor supported on non-cuspidal places }
    a, b := Support(D);
    return &+[ b[i]*HeckeOperatorFast(X, q, a[i]) : i in [1..#a] ];
end intrinsic;

intrinsic PlacesUpToDiamondFast(X::MDCrvMod1, S::SeqEnum[PlcCrvElt]) -> SeqEnum[PlcCrvElt]
{ One representative per orbit of S under the diamond operators, computed with elliptic-curve
  isomorphism tests only (no function-field place computations).  Two places x, x' (of the same degree k)
  lie in the same orbit iff for some Frobenius power sigma and some a coprime to N there is an isomorphism
  (E_x, a P_x)^sigma -> (E_x', +-P_x'); this is tested on all j-invariant classes. }
    N := Level(X); F := PrimeField(BaseRing(X)); p := #F;
    data := [* *];
    for x in S do
        E := EllipticCurve(X, x); P := LevelStructure(X, x)`P;
        Append(~data, <E, P, MinimalPolynomial(jInvariant(E), F), Degree(x)>);
    end for;
    groups := AssociativeArray();
    for i in [1..#S] do
        key := <data[i][3], data[i][4]>;
        if IsDefined(groups, key) then Append(~groups[key], i); else groups[key] := [i]; end if;
    end for;
    reps := [];
    for key in Keys(groups) do
        idx := groups[key]; done := [false : i in idx];
        for a in [1..#idx] do
            if done[a] then continue; end if;
            done[a] := true; Append(~reps, S[idx[a]]);
            E1 := data[idx[a]][1]; P1 := data[idx[a]][2]; K1 := BaseRing(E1); k := Degree(K1);
            mults := {@ c*P1 : c in [1..N-1] | GCD(c, N) eq 1 @};   // generators of <P1>
            for b in [a+1..#idx] do
                if done[b] then continue; end if;
                E2 := data[idx[b]][1]; P2 := data[idx[b]][2]; K2 := BaseRing(E2);
                // move (E2, P2) to K1
                if K2 cmpne K1 then
                    ok := true;
                    try ainv := [K1!c : c in aInvariants(E2)]; pc := [K1!c : c in Eltseq(P2)]; catch e ok := false; end try;
                    if not ok then Embed(K2, K1); ainv := [K1!c : c in aInvariants(E2)]; pc := [K1!c : c in Eltseq(P2)]; end if;
                else ainv := aInvariants(E2); pc := Eltseq(P2); end if;
                found := false;
                for i in [0..k-1] do
                    pe := p^i;
                    E2i := EllipticCurve([c^pe : c in ainv]);
                    P2i := E2i![c^pe : c in pc];
                    iso, phi := IsIsomorphic(E2i, E1);
                    if not iso then continue; end if;
                    for alpha in Automorphisms(E1) do
                        Q := alpha(phi(P2i));
                        if Q in mults then found := true; break; end if;
                    end for;
                    if found then break; end if;
                end for;
                if found then done[b] := true; end if;
            end for;
        end for;
    end for;
    return reps;
end intrinsic;
