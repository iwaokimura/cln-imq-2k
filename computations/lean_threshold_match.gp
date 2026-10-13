/* Match the Lean thresholds T_N (B4.ClassNumber.classNumber_gt_N: log|disc K| >= T_N => h_K > N)
   with the ranges of |d| covered by the Mosunov--Jacobson tables and the qsieve runs (2026-10-10).
   Ranges are closed intervals [a, b] as printed in qsieve/logs/<run>/stdout.txt. */

/* T_N exactly as in lean/B4ClassNumber.lean */
thresholds() = {
  return([[100, 286787/10000], [200, 150729/5000], [500, 160029/5000], [1000, 334757/10000], [2000, 350131/10000]]);
};

/* [name, N, a, b]; MJ = Mosunov--Jacobson tables (complete class number tables; the 2000 only
   marks "any N <= 2000"; the h <= 2000 extraction is mj_extract_h2000.txt), used for |d| < 6*2^28 */
runs() = {
  return([["MJ", 2000, 3, 6*2^28 - 1],
          ["gap200", 200, 1610612736, 1099511627776],
          ["main200", 200, 1099511627776, 2560000000000000],
          ["gap1000", 1000, 1610612736, 1099511627776],
          ["main1000", 1000, 1099511627776, 260000000000000],
          ["ext1000", 1000, 260000000000000, 320000000000000],
          ["ext1000b", 1000, 320000000000000, 350000000000000],
          ["gap2000", 2000, 1610612736, 1099511627776],
          ["main2000", 2000, 1099511627776, 1650000000000000]]);
};

/* one pass: extend top by any run with class bound >= N starting at or below top + 1 */
extend_once(N, top) = {
  my(R = runs(), t = top);
  for(i = 1, #R, if(R[i][2] >= N && R[i][3] <= t + 1 && R[i][4] > t, t = R[i][4]));
  return(t);
};

/* largest b such that [3, b] is covered without gaps by runs with class bound >= N */
covered_to(N) = {
  my(top = 2, nxt = extend_once(N, 2));
  while(nxt > top, top = nxt; nxt = extend_once(N, top));
  return(top);
};

check(N, T) = {
  my(top = covered_to(N), E = exp(T), ok);
  /* every |d| with log|d| < T satisfies |d| <= floor(exp(T)) (exp(T) is not an integer) */
  ok = (floor(E) <= top) && (log(top + 1) > T);
  printf("N = %4d  T_N = %-12s exp(T_N) = %.6e  covered up to %.4e  margin x%.4f  %s\n",
         N, Str(T), E, top, top / E, if(ok, "OK", "GAP"));
  return(ok);
};

run() = {
  my(Th = thresholds(), allok = 1);
  default(realprecision, 60);
  for(i = 1, #Th, allok = allok && check(Th[i][1], Th[i][2]));
  print(if(allok, "ALL THRESHOLDS COVERED", "COVERAGE GAP"));
  return(allok);
};

run();
