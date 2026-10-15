\\ Check (b) of the paper, Section "Small discriminants": the sampled entries "d h" with
\\ 1000 < h <= 2000 (random_check_h2000_sample.txt, made by random_check_h2000_sample.py) satisfy
\\ isfundamental(-d) and qfbclassno(-d) == h. qfbclassno is documented as correct for |D| < 2*10^10 (PARI
\\ manual), and every d here is below 2^30.
\\ Run from computations/:  gp -q -f random_check_h2000.gp < /dev/null > random_check_h2000.txt

if(type(SAMPLEFILE) != "t_STR", SAMPLEFILE = "random_check_h2000_sample.txt");

\\ 1 if the line "d h" passes, 0 otherwise; returns [ok, d]
checkline(s) = {
  my(w = strsplit(s, " "), d, h, ok = 1);
  if(#w != 2, error(Str("bad line: ", s)));
  d = eval(w[1]); h = eval(w[2]);
  if(d >= 2*10^10, ok = 0);
  if(!(1000 < h && h <= 2000), ok = 0);
  if(!isfundamental(-d), ok = 0);
  if(qfbclassno(-d) != h, ok = 0);
  if(!ok, print("MISMATCH d = ", d, " h = ", h));
  return([ok, d]);
};

run() = {
  my(v = readstr(SAMPLEFILE), n = #v, bad = 0, dmax = 0, r);
  if(n == 0, error("empty sample file"));
  for(i = 1, n, r = checkline(v[i]); if(!r[1], bad++); dmax = max(dmax, r[2]));
  print("entries checked: ", n, ", largest d: ", dmax, ", mismatches: ", bad);
  if(bad == 0 && n == 2000, print("RESULT: PASS"), print("RESULT: FAIL"));
  return(bad);
};

run();
