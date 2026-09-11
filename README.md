# quintic-torsion

Code and logs accompanying the paper *Classification of torsion of elliptic curves over quintic
fields*.

The manuscript names no scripts or logs; the table in
[Which script proves what](#which-script-proves-what) is the authoritative map from each
statement that rests on a computation to the script that verifies it and the log that script
produced. Every log in `logs/` was produced by the code in this repository as it now stands, and
every one of them can be regenerated with [`verify_all.sh`](#reproducing-the-computations).

## Getting the code

The Magma code depends on [mdmagma](https://github.com/koffie/mdmagma), which supplies the
moduli-theoretic routines (`ModuliPoint`, `LevelStructure`, `HeckeOperator`, `DiamondOperator`,
`CuspOrbitsQ`) and, through its own `Magma` submodule, Sutherland's optimised models of
`X_1(N)`. One script also uses Sutherland's
[GL2 package](https://github.com/AndrewVSutherland/Magma) for point counting. Both are pinned as
submodules, so that the results can be reproduced exactly.

```bash
git clone https://github.com/F-Najman/quintic-torsion
cd quintic-torsion
git submodule update --init                     # mdmagma and gl2
git -C mdmagma submodule update --init Magma    # Sutherland's models, used by mdmagma
```

Do not use `git clone --recurse-submodules`: mdmagma has a further submodule
`tests/magma-unittest` registered under an SSH URL (`git@github.com:...`), so a full recursive
clone can fail without a GitHub SSH key. The test submodule is unused here; the two
commands above initialise the required packages and skip it. (If you do want everything, add
`-c url.https://github.com/.insteadOf=git@github.com:` to the clone.)

The pinned commits are mdmagma `d1c019c6` (2026-06-13) with its `Magma` submodule at `6a5a68a8`,
and the GL2 package at `e70690a` (2026-08-15). The latter two are *different* checkouts of the
same repository on purpose: mdmagma pins an August 2024 commit that predates `gl2points.m`, so
`gl2_point_counts.m` attaches the separate up-to-date copy in `gl2/` while every other script
attaches mdmagma's pinned one. Leave both as they are.

## Running the computations

All scripts are run from the repository root; the `AttachSpec` paths and the relative paths
`data/...` are resolved from there. Everything was run with Magma V2.29-4 and, for the Python
scripts, with Sage 10's `python3`. Python 3 with SymPy is sufficient: install SymPy with
`python3 -m pip install sympy` if needed. `lmfdb_ranks.py` uses only the standard library.
The shell driver requires Bash 4 or later and GNU command-line tools, as supplied on the Linux
server used for these computations. Magma commands use `-n` to suppress personal startup files.

Several drivers take parameters, passed as `magma -n -b Name:=value script.m`:

* `hecke_sieve_deg5.m`, `hecke_sieve_deg5_v6.m` — the Hecke sieve. Parameters `N`, `p`, `Qs`,
  `D`, `M`, `MemGB`, `Shard`, `NShard`; `M:=2` selects `X_1(2,N)`. The congruence condition on
  `q` is computed from the model and reported on the `CUSPFIELDS` and `CC` lines of the log.
* `hecke_sieve_twisted_v6.m` — the twisted sieve, with the same parameters plus `As` (the
  diamond elements `a`), `Hs` (generators of `H`) and `SkipCusps`.
* `direct_analysis.m`, `direct_analysis_X11.m` — parameters `N`, `Ps`, `D`, `MemGB`, `MaxLift`.
* `analyze_survivors.m` — parameters `N`, `p`, `SURV`.
* `count_Y1_points.m` — parameters `N`, `p`, `M`, `D`.
* `torsion_over_Fq.m` — parameters `Ns` (the levels, comma-separated), `Ps` and `K`. The
  defaults are *not* the values used for the paper; take the command from `jobs.txt`.
* `lmfdb_ranks.py` — no arguments: it verifies the archived LMFDB data offline. With `--fetch`
  it refetches from the LMFDB and rewrites the three files in `data/`.

For example:

```bash
magma -n -b N:=45 p:=7 Qs:=11,13,17,19 D:=5 M:=1 MemGB:=12 Shard:=0 NShard:=6 hecke_sieve_deg5_v6.m
magma -n -b N:=63 p:=5 Qs:=11,13,17 As:=5 Hs:=8 D:=5 M:=1 SkipCusps:=1 MemGB:=20 Shard:=0 NShard:=8 hecke_sieve_twisted_v6.m
magma -n -b N:=30 Ps:=7 D:=5 MemGB:=20 direct_analysis.m
magma -n -b verify_sporadic_curves.m
python3 lmfdb_ranks.py
```

Magma may buffer its output, so a terminated run can leave an empty or incomplete log.
Some Magma errors also return exit status 0. Check both the exit status and the closing marker:
every script prints a marker on its last non-blank line when it finishes. The third column of
`jobs.txt` gives the marker for each log; they are `SIEVE_DONE` for a sieve, `DIRECT_DONE` for a
direct analysis, and `ANALYZE_DONE`, `CHARKERNELS_DONE`, `COUNT_DONE`, `CUSPGROUP_DONE`,
`GLOBALTABLE_DONE`, `GL2_POINT_COUNTS_DONE all_agree=true`, `GROUPLIST_DONE`,
`NO_DEGREE_FIVE_RATIONAL_FUNCTION_INDEPENDENTLY_VERIFIED` (`pencils_2_18.m`),
`PLACESCHECK_DONE all_consistent=true`, `RANKS_DONE OK`, `TESTFAST_DONE`, `TESTORB_DONE`,
`ALL CHECKS PASSED` (`verify_sporadic_curves.m`) and `DONE` (`torsion_over_Fq.m`) for the rest.

A sieve log is delimited by the markers `SETUP`, `CUSPS`, `CUSPFIELDS`, `CC`, `NONCUSP`,
`QLIST`, `REPS`, `DEGREES`, `TYPE`, `PROGRESS`, `RESULT`, `SURVIVOR`, `SURVIVOR_DATA`, `SUMMARY`
and `SIEVE_DONE`; a direct-analysis log by `SETUP`, `J`, `PRIME`, `CUSPIDAL`, `CANDIDATES`,
`CANDIDATES_NONCUSPIDAL`, `KNOWN`, `MATCHED_KNOWN`, `POINT`, `RESULT` and `DIRECT_DONE`.

## Reproducing the computations

`jobs.txt` lists each log file, the command that produces it, and its closing marker. An optional
fourth column gives an expected result as an extended regular expression.

Run the computations with:

```bash
./verify_all.sh                 # every job, one at a time
./verify_all.sh -j 4            # four at a time
./verify_all.sh X1_45           # only the jobs whose log path contains X1_45
./verify_all.sh -j 4 counts     # both
git diff                        # what the rerun changed
```

The driver overwrites the selected logs in place; `git diff` compares the new output with the
committed run. Do not change the parameters in `jobs.txt`: they are the ones the
committed logs were produced with, and `Shard`/`NShard` in particular partition the work, so a
shard log only means anything together with its siblings.

A job passes the automated checks only if its command exits 0, its last non-blank line is the
expected marker (optionally followed by a space and details), and any result expression matches.
The sieve jobs check their expected survivor totals, including the five survivors on X_1(28).
Failures are listed at the end and give a nonzero exit status. Missing or malformed job lists,
invalid options and filters matching no jobs also give a nonzero status. Use `git diff` to check
the detailed numerical results as described below.

When Magma jobs are selected, the driver first attaches mdmagma and `fast_hecke.m` in one process,
then the separate GL2 package in another. This sequential step creates the signature files before
parallel jobs use them; concurrent first-time attachment can cause Magma signature-cache errors.
Python-only selections run without Magma or its submodules.

The driver's regression tests and the offline rank-checker tests run with
`python3 -m unittest discover -s tests`; they do not require Magma or network access.

A full rerun costs about 200 hours of CPU time, almost all of it on `X_1(45)`, `X_1(57)`,
`X_1(63)` and `X_1(65)`; the 23 shards of those four curves are independent and can be run
concurrently. Everything else together takes about six hours, of which four and a half are
`X_1(42)`.

What a successful reproduction should change, and nothing else:

* timing figures, including the `time=...` fields and the timings printed by the fast-routine
  comparisons;
* whitespace, such as a final blank line;
* whatever a different version of Magma or of mdmagma prints differently, which can include the
  printed form of a model or of an ideal, and the order of the elements within a listed set.

Everything else is a genuine discrepancy and should be reported: the counts on the `CUSPS`,
`NONCUSP`, `REPS`, `DEGREES` and `RESULT` lines, the primes on the `QLIST` and `CC` lines, the
fields on `CUSPFIELDS`, every `SURVIVOR` line, the totals on `SUMMARY`, and the presence of the
closing marker. The conclusions those lines have to carry are:

* every sieve summary reports `total_survivors=0`, with the one exception of `X_1(28)` at `p=3`, which
  leaves five survivors, one of type `[4]` and four of type `[5]`; `analyze_survivors.m` then
  matches one of them to the known point and eliminates the other four;
* the direct analyses report `0 false positives`, `0 pencils` and `0 all-cuspidal effective
  divisors` throughout, and find non-cuspidal effective divisors only on `X_1(2,18)`, where
  there are `18`, listed on the `POINT` lines; on `X_1(28)` the six known points exhaust the
  non-cuspidal candidates (`MATCHED_KNOWN: ... 0 non-cuspidal candidate classes remain`);
* `lmfdb_ranks.py` prints `RANKS_DONE OK`, having reproduced both derived data files from the
  archived newform records.

## Which script proves what

Numbering refers to the manuscript.

| Statement | Script | Log |
|---|---|---|
| Lemma 3.1 (the list of 45 groups) | `group_list.py` | `logs/group_list.log` |
| Table 2 (constants of the global method) | `global_table.py` | `logs/global_table.log` |
| Section 7 and Table 4 (the analytic ranks quoted from the LMFDB) | `lmfdb_ranks.py` | `logs/lmfdb_ranks.log` |
| Proposition 4.2, condition (1); Remark 4.3 (character kernels) | `char_kernels_all.m` | `logs/char_kernels_all.log` |
| Proposition 5.2 (n = 27, 35, 39, 50) | `torsion_over_Fq.m` | `logs/torsion_over_Fq.log` |
| Proposition 6.3 and Table 3 (Hecke sieve) | `hecke_sieve_deg5.m`, `hecke_sieve_deg5_v6.m` | `logs/sieve/X1_26_p7.log`, `X1_32_p3.log`, `X1_33_p7.log`, `X1_34_p3.log`, `X1_38_p3.log`, `X1_42_p5.log`, `X1_2_22_p3.log`, `X1_45_p7_v6_shard{0..5}.log` |
| Remark 6.4 (the congruence condition on q, per curve) | `hecke_sieve_deg5_v6.m` | the `CUSPFIELDS` and `CC` lines of the sieve logs above |
| Proposition 7.7 and Table 5 (twisted sieve, n = 57, 63, 65) | `hecke_sieve_twisted_v6.m` | `logs/sieve/X1_57_p5_v6_shard{0..5}.log`, `X1_63_p5_v6b_shard{0..7}.log`, `X1_65_p3_v6_shard{0..2}.log` |
| Remark 8.3 (the base cusp must be a rational one) | `cuspgroup_check.m` | `logs/cuspgroup_check.log` |
| Proposition 8.4 (Z/2 x Z/20 and Z/2 x Z/24) | `direct_analysis_X11.m` | `logs/direct_2_20.log`, `logs/direct_2_24.log` |
| Remark 8.5 (the X_1(26) cross-check) | `direct_analysis.m` | `logs/direct_26.log` |
| Proposition 8.6 (X_1(28)) | `direct_analysis.m` | `logs/direct_28.log` |
| Remark 8.7 (the Hecke sieve at p = 3 on X_1(28)) | `analyze_survivors.m` | `logs/sieve/X1_28_p3.log`, `logs/analyze_28_3.log` |
| Proposition 8.8 (X_1(30)) | `direct_analysis.m` | `logs/direct_30.log` |
| Proposition 8.9 (X_1(2,18)) | `direct_analysis_X11.m` | `logs/direct_2_18.log` |
| Remark 8.10 (the 27 moving cuspidal pencils) | `pencils_2_18.m` | `logs/pencils_2_18.log` |
| Propositions 9.1 and 9.3 and Table 7 (the sporadic curves, their fields and conductors, Z/36) | `verify_sporadic_curves.m` | `logs/verify_sporadic_curves.log` |
| Section 10.1, Lemmas 10.1-10.2 (the fast routines) | `fast_hecke.m`, `test_fast_hecke.m`, `test_fast_orbits.m` | `logs/test_fast_hecke.log`, `logs/test_fast_orbits.log` |
| The place counts of Tables 3 and 5, verified independently of any model | `count_Y1_points.m` | `logs/counts/*.log` (18 files, one per curve and prime) |
| The same place counts, recomputed with Sutherland's GL2 package | `gl2_point_counts.m` | `logs/gl2_point_counts.log` |
| Completeness of the place enumeration, checked within the model | `check_places_count.m` | `logs/check_places_count.log` |
| Completeness of the F_q enumerations underlying Lemma 2.3 | `torsion_over_Fq.m` | `logs/torsion_over_Fq.log` |

The last four rows support computations that are *not* written up in the manuscript: they check
that the enumeration of closed points of degree at most 5 is complete, which every sieve
conclusion silently assumes, and that the enumerations behind Lemma 2.3 cover every prime power
used. They are recorded here because the results depend on them.

## The archived data

`data/` holds the inputs that would otherwise have to be fetched over the network, so that every
check in this repository can be rerun offline:

* `lmfdb_newforms_cache.json` — the raw LMFDB records of the weight-2 newforms of every level
  dividing one of the 41 levels of the paper: label, character orbit and order, dimension,
  analytic rank and whether that rank is proved.
* `lmfdb_ranks.json`, `lmfdb_ranks_summary.txt` — the derived decomposition of each `J_1(N)`,
  with the analytic rank of each factor and the forms of positive rank.
* `surv_28_3.txt` — the five survivors of the sieve on `X_1(28)` at `p = 3`, the input of
  `analyze_survivors.m`. To reconstruct this input, take each `data=...` expression on the
  `SURVIVOR_DATA` lines of the sieve log, join any wrapped lines, and put one expression on
  each line of the file.

`python3 lmfdb_ranks.py` recomputes the second group from the first and checks it against what
is committed, together with the consistency check that the dimensions of the factors add up to
the genus of `X_1(N)`; `--fetch` refetches everything from the LMFDB instead.

## Hardware

The computations were run on a server at the University of Zagreb with an AMD EPYC 9175F CPU
(16 cores, 32 threads) and 384 GB of RAM, using Magma V2.29-4. The total cost was about 203
hours of CPU time, of which 197 hours were spent on the four curves `X_1(45)`, `X_1(57)`,
`X_1(63)` and `X_1(65)`. Runs were given memory limits of 8-24 GB.
