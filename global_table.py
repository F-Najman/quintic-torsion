# Recomputes the constants of the "global method" (Derickx-Najman, Prop. 4.5 / 6.1 / 7.1)
# for d = 5:  b(n) = (325/2^15) * [PSL_2(Z):Gamma_1(n)/{+-1}] / k_q,  q = 3.
from fractions import Fraction
from sympy import totient, primefactors

def idx_SL2(n):                      # [SL_2(Z) : Gamma_1(n)]
    r = n*n
    for p in primefactors(n): r = r*(p*p-1)//(p*p)
    return r
def idx_PSL(n):                      # [PSL_2(Z) : image of Gamma_1(n)] = idx_SL2 / 2  (n>2)
    return idx_SL2(n)//2
def ordd(a,n):                       # order of <a> in (Z/n)^* / {+-1}
    k=1; x=a%n
    while x!=1 and x!=n-1: x=x*a%n; k+=1
    return k

C = Fraction(325, 2**15)
# The elements a are those of the published version, Derickx-Najman, Crelle 829 (2025),
# Table 2 (n = 91, 121, 143, 169, 187, 221, 289) and Table 3 (n = 95, 119, 125, 133, 209, 247,
# 323, 361).  NB the arXiv preprint arXiv:2412.16016 uses a = 56 at n = 121 and a = 3 at n = 85;
# the published version uses a = 2 in both cases.  Either choice of a at n = 121 gives k_3 = 8
# and the same b(121); only the order of <a> differs (11 for a = 56, 55 for a = 2).
rows = [ (91,3), (121,2), (143,67), (169,3), (187,122), (221,3), (289,3),
         (95,3**12), (119,3), (125,3), (133,3**6), (209,3**5), (247,3**12), (323,3**8), (361,3) ]
dcm = {91:24,121:110,143:120,169:52,187:160,221:96,289:136,
       95:72,119:96,125:50,133:36,209:180,247:72,323:288,361:114}
print(f"{'n':>4} {'a mod n':>8} {'ord<a>':>7} {'idx':>6} {'k_3':>4} {'b(n)':>8} {'b>5':>5} {'ord|5':>6} {'d_CM':>5}")
allok = True
for n,a in rows:
    am = a % n
    k3 = 7 if am in (3 % n, pow(3,-1,n)) else 8
    b = C * Fraction(idx_PSL(n), k3)
    o = ordd(am, n)
    ok = (b > 5) and (5 % o != 0) and (dcm[n] > 5)
    allok &= ok
    print(f"{n:>4} {am:>8} {o:>7} {idx_PSL(n):>6} {k3:>4} {float(b):>8.3f} {str(b>5):>5} {str(5%o==0):>6} {dcm[n]:>5}")
print("\nall cases give a valid degree-5 conclusion:", allok)
# Abramovich bound for the M3 cases
print("\nAbramovich gon_C > (325/2^15)*idx  for n = 77, 85, 57, 63, 65:")
for n in (77,85,57,63,65):
    print(f"  n={n:>3}  idx={idx_PSL(n):>5}  bound={float(C*idx_PSL(n)):8.3f}")
assert allok, "a global-method case does not give a valid degree-5 conclusion"
print("GLOBALTABLE_DONE")
