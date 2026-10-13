\\ Tests for postproc.gp: classno_upto against qfbclassno (unconditional below 2*10^10), and timings.
\\ Run: gp -q postproc_test.gp < /dev/null   (prints "POSTPROC TEST PASS" or "... FAIL")

NO_RUN = 1;
read("postproc.gp");

\\ one d: full value and the threshold behaviour at N = h-1, h, 1000; returns the number of mismatches
check_one(d) = {
  my(h = qfbclassno(-d), bad = 0);
  if(classno_upto(d, 10^9) != h, bad++);
  if(h > 1 && classno_upto(d, h - 1) != h, bad++);
  if(classno_upto(d, h) != h, bad++);
  if(classno_upto(d, 1000) != min(h, 1001), bad++);
  if(bad, print("MISMATCH d = ", d, ", h = ", h));
  return(bad);
};

\\ all fundamental d in [5, X]
test_exhaustive(X) = {
  my(n = 0, bad = 0);
  for(d = 5, X,
    if(isfundamental(-d), n++; bad += check_one(d)));
  print("exhaustive 5 <= d <= ", X, ": ", n, " fundamental d, mismatches ", bad);
  return(bad);
};

\\ ns random fundamental d in [lo, hi]
test_random(lo, hi, ns) = {
  my(n = 0, bad = 0, d);
  setrand(20261009);
  while(n < ns,
    d = lo + random(hi - lo);
    if(isfundamental(-d), n++; bad += check_one(d)));
  print("random ", ns, " fundamental d in [", lo, ", ", hi, "]: mismatches ", bad);
  return(bad);
};

\\ fields with small h near the top of the tables: genuine h <= 1000 must be found exactly
test_list(fname, ns) = {
  \\ lines are "d h": readvec would evaluate "d h" as one integer (whitespace is ignored), so split
  my(v = readstr(fname), n = 0, bad = 0, d, h, w);
  setrand(1);
  while(n < ns,
    w = strsplit(v[1 + random(#v)], " ");
    d = eval(w[1]); h = eval(w[2]);
    if(d <= 4, next);
    n++;
    if(classno_upto(d, 1000) != h, bad++; print("LIST MISMATCH d = ", d)));
  print("list ", fname, ": ", ns, " random entries, mismatches ", bad);
  return(bad);
};

\\ timings at d ~ 2.6e14: typical residual (h > N, early exit), and the full prime loop
time_large(ns) = {
  my(t, d, n = 0, X = 260000000000000, D, pmax, cnt = 0, S = Map(), e, g);
  setrand(7);
  t = getabstime();
  while(n < ns,
    d = X + random(10^12);
    if(isfundamental(-d), n++; if(classno_upto(d, 1000) != 1001, print("UNEXPECTED small h at d = ", d))));
  print("d ~ 2.6e14, N = 1000: ", ns, " fundamental d, ", (getabstime() - t) / ns, " ms each (all h > 1000)");
  \\ worst case cost: one pass over all split/ramified p <= sqrt(d/3) with a lookup (no group growth)
  d = X + 3; while(!isfundamental(-d), d++);
  D = -d; pmax = sqrtint(d \ 3);
  e = qfbprimeform(D, 1); mapput(S, qkey(e), 1);
  t = getabstime();
  forprime(p = 2, pmax,
    if(kronecker(D, p) != -1,
      g = qfbprimeform(D, p);
      if(mapisdefined(S, qkey(g)), cnt++)));
  print("full prime loop at d = ", d, " (p <= ", pmax, "): ", getabstime() - t, " ms");
  return(0);
};

run() = {
  my(bad = 0);
  bad += test_exhaustive(20000);
  bad += test_random(10^5, 2*10^10, 300);
  bad += test_list("../computations/mj_h200_list.txt", 300);
  time_large(20);
  print(if(bad, "POSTPROC TEST FAIL", "POSTPROC TEST PASS"));
  return(bad);
};

run();
