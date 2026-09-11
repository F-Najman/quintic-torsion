/* gl2_point_counts.m -- third, independent recomputation of the reference point counts, using
   Sutherland's GL2 package (https://github.com/AndrewVSutherland/Magma, file gl2points.m).

   That package counts #X_H(F_q) and #Y_H(F_q) from Frobenius similarity classes and weighted
   class numbers, whereas count_Y1_points.m enumerates j-invariants and twists directly;
   the two are independent implementations of the same moduli-theoretic count, and neither uses
   a model of the modular curve.

   X_1(m,n), m | n, is X_H for the pointwise stabiliser in GL(2,Z/n) of the level structure
   (P,Q) = ((n/m)e_1, e_2) of type Z/m x Z/n on E[n], namely
        H = { [a,0;c,1] : a = 1 mod m,  c = 0 mod m }.
   The genus of X_H is printed as a check on this identification.

   Usage: magma -n -b gl2_point_counts.m   (needs the current AndrewVSutherland/Magma checkout) */
SetColumns(0);
AttachSpec("gl2/magma.spec");

function LevelSubgroup(m,n)
    G := GL(2,Integers(n));
    gens := [ G![1,0,m,1] ]
        cat [ G![a,0,0,1] : a in [x : x in [1..n] | GCD(x,n) eq 1 and (x-1) mod m eq 0] ];
    return sub<G | gens>;
end function;

// <m, n, p, expected #Y_1(m,n)(F_{p^d}) for d = 1..5>, as independently computed in logs/counts/
pairs := [
<1,26,7,[0,84,372,2496,16560]>, <1,28,3,[0,0,6,48,270]>, <1,30,7,[0,40,384,2448,15840]>,
<1,32,3,[0,0,24,32,80]>, <1,33,7,[0,0,120,2640,18220]>, <1,34,3,[0,0,0,104,160]>,
<1,38,3,[0,0,9,0,360]>, <1,42,5,[0,0,12,732,3240]>, <1,45,7,[0,48,360,1440,16380]>,
<1,57,5,[0,0,216,324,3780]>, <1,63,5,[0,0,36,432,3600]>, <1,65,3,[0,0,0,48,480]>,
<2,18,5,[0,0,144,612,3060]>, <2,20,3,[0,0,0,160,240]>, <2,20,7,[0,32,384,2848,16080]>,
<2,22,3,[0,0,0,0,300]>, <2,24,5,[0,0,48,384,3360]>
];

allok := true;
for t in pairs do
    m,n,p,exp := Explode(t);
    H := LevelSubgroup(m,n);
    assert GL2Level(H) eq n and #H eq (n div m)*#[x : x in [1..n] | GCD(x,n) eq 1 and (x-1) mod m eq 0];
    ycnt := [ &+GL2jCounts(H,p^d) : d in [1..5] ];
    ok := ycnt eq exp; allok and:= ok;
    printf "GL2COUNT X_1(%o,%o) p=%o: genus %o | #Y(F_{p^d}) = %o | reference = %o | %o\n",
        m, n, p, GL2Genus(H), ycnt, exp, ok select "agree" else "MISMATCH";
end for;
printf "GL2_POINT_COUNTS_DONE all_agree=%o\n", allok;
quit;
