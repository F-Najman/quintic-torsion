/* char_kernels_all.m -- for each level N and each LMFDB character orbit label with a positive
   analytic rank newform (data/lmfdb_ranks_summary.txt), compute the kernel of the character
   (all Conrey indices with that orbit label, via Sutherland's ConreyCharacterOrbitLabel) and list
   diamond operators <a> (a in the joint kernel) with their order in (Z/N)^* modulo sign.
   Also report whether the a used in arXiv:2412.16016 Table 6.1 lies in the kernel. */
SetColumns(0);
AttachSpec("mdmagma/Magma/magma.spec");
cases := [ <85, ["j"], 3>, <91, ["g","u"], 3>, <95, ["l"], 3^12>, <133, ["f","s"], 3^6>, <143, ["h"], 67>,
           <187, ["g"], 122>, <209, ["f"], 3^5>, <247, ["be"], 3^12>, <323, ["k"], 3^8> ];
for cs in cases do
  N, labels, apaper := Explode(cs);
  units := [a : a in [1..N-1] | GCD(a,N) eq 1];
  ZN := Integers(N);
  function OrdPM(a) k := 1; x := ZN!a; while x ne 1 and x ne -1 do x *:= a; k +:= 1; end while; return k; end function;
  joint := Seqset(units);
  for lab in labels do
    idx := [n : n in units | ConreyCharacterOrbitLabel(N, n) eq Sprintf("%o.%o", N, lab)];
    n0 := idx[1];
    ker := { a : a in units | ConreyCharacterValue(N, n0, a) eq 1 };
    ord := Min([k : k in [1..N] | &and[ConreyCharacterValue(N,n0,a)^k eq 1 : a in units]]);
    printf "N=%o orbit %o.%o: Conrey indices %o, order %o, #ker=%o, chi(-1)=%o\n", N, N, lab, idx, ord, #ker, ConreyCharacterValue(N,n0,N-1);
    joint meet:= ker;
  end for;
  ap := apaper mod N;
  printf "N=%o: joint kernel order %o; arXiv quartic choice a=%o (=%o mod N) in joint kernel: %o, ord<a>=%o\n", N, #joint, apaper, ap, ap in joint, OrdPM(ap);
  good5 := Sort([<a, OrdPM(a)> : a in joint | OrdPM(a) gt 5]);
  good4 := Sort([<a, OrdPM(a)> : a in joint | 4 mod OrdPM(a) ne 0]);
  printf "N=%o: a in joint kernel with ord>5 (for d=5): %o\n", N, [t : t in good5][1..Min(12,#good5)];
  printf "N=%o: a in joint kernel with ord not dividing 4 (for d=4): first few %o (total %o)\n\n", N, [t : t in good4][1..Min(8,#good4)], #good4;
end for;
print "CHARKERNELS_DONE";
quit;
