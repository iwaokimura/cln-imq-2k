\\ Effective constant in [SZ] (OAI: Uniform exclusion of Landau--Siegel zeros).
\\ Computes delta*(ell) = admissible lower bound for (1-beta)*log q, for two variants:
\\   A: the cube E_N of [SZ], with optimized interpolation degrees (lambda = 6.35);
\\   B: rectangular box N x N' x N x N', N' = ceil(N/sqrt q)   (needs Lemma 3 of [SZ] for boxes).
\\ Then the class-number constant and discriminant bounds D(N).
\\ The "Mertens route" (deltastarM) uses the constants of Rosser--Schoenfeld; certify_c2.gp certifies it
\\ (cited in the Remark after Proposition 6 of the paper), and certify_c2_lean.gp does the same for the
\\ formalized form. Here this file is only read, with NO_RUN = 1, by certify_c2.gp, certify_c2_lean.gp
\\ and lean_grid.gp.

if(default(parisize) < 400000000, default(parisize, 400000000));
default(realprecision, 38);
\\ theta(x) < THETA_C * x for all x > 0: Rosser--Schoenfeld 1962, Thm 9, (3.32), with 1.01624 (checked
\\ against the original). A wrapper may set THETA_C before read() (robustness check: 1.02).
if(type(THETA_C) == "t_POL", THETA_C = 1.01624);

\\ ---------- numerical lemmas ----------

\\ g(s) = -zeta'/zeta(s) - 1/(s-1); we need -Euler <= g(s) <= 0 on (1, 3/2].
check_zeta_logder() = {
  my(gmin = 1e9, gmax = -1e9, s, g, k, j);
  for(k = 1, 8,
    for(j = 1, 9,
      s = 1 + j * 10.^(-k);
      if(s <= 1.5,
        g = -derivnum(x = s, zeta(x)) / zeta(s) - 1/(s-1);
        gmin = min(gmin, g); gmax = max(gmax, g))));
  forstep(s = 1.01, 1.5, 0.001,
    g = -derivnum(x = s, zeta(x)) / zeta(s) - 1/(s-1);
    gmin = min(gmin, g); gmax = max(gmax, g));
  print("check: g(s) = -zeta'/zeta - 1/(s-1) on grid in (1,1.5]: min = ", gmin, "  max = ", gmax, "  (need >= -Euler = ", -Euler, " and <= 0)");
  return(gmin >= -Euler && gmax <= 0);
};

\\ K1 = Euler + sum_p log p/(p(p-1)) (+ tail bound beyond 10^7)
compute_K1() = {
  my(S = 0., X = 10^7);
  forprime(p = 2, X, S += log(p)/(p*(p-1)));
  S += (log(X) + 1)/X;
  print("sum_p log p/(p(p-1)) <= ", S);
  return(Euler + S);
};

\\ Lambda_H = sum_{p <= H} log p / p, computed exactly (floating) for the listed H
compute_LambdaH(Hs) = {
  my(res = vector(#Hs), S = 0., i = 1, last = 1);
  for(i = 1, #Hs,
    forprime(p = last + 1, Hs[i], S += log(p)/p);
    last = Hs[i];
    res[i] = S);
  return(res);
};

\\ R(ell) = upper bound for sum_{p | q} log p / p over q <= e^ell:
\\ q has at most k prime factors, k = max{k : p_k# <= q}, so the sum is at most the sum of the k largest
\\ values of log p/p. These are 3, 2, 5, 7, ... (log 3/3 > log 2/2): the first k primes for k >= 2, but
\\ log(3)/3 for k = 1 (q = 3, 4, 5). Corrected 2026-10-09 (found by an independent recheck); before, k = 1 gave log(2)/2.
Rbound(ell) = {
  my(L = 0., S = 0., k = 0);
  forprime(p = 2, 10^6,
    L += log(p);
    if(L > ell, return(if(k == 1, log(3)/3, S)));
    S += log(p)/p; k++);
  return(S);
};

\\ ---------- the master inequality ----------
\\ Returns delta* for given (ell, eta, Lu = log U, H, variant), or -1 if the bracket is negative.
\\ lam = 6.35, lam^3 = 256.05 > 256.
deltastar(ell, eta, Lu, H, LH, K1, R, variant) = {
  my(lam = 6.35, logN, tau, tau2, B, S1M, rho, epsth, Aterm, size, extra, br);
  epsth = 151.3 / Lu^4;
  if(variant == "A", logN = 3*Lu/4, logN = 3*Lu/4 + ell/4);
  tau = (3*exp(logN - Lu) + exp(-Lu)) * (1 + 2*H) / (3*lam*H^(2/3));
  B = 3*lam*H^(-1/3)*exp(Lu)*(1 + tau);
  S1M = exp(Lu) * H^(2/3) / (9*lam^2*(1 + tau + 2*(1 + tau)/B)^2) - 1/2;  \\ (B+2)/(B/(1+tau)) = 1+tau+2(1+tau)/B
  rho = B / S1M;
  if(variant == "A", size = 3*Lu/4 + ell/2 + log(8), size = 3*Lu/4 + ell/4 + log(4.84));
  extra = ((1 + epsth) + 1.5*Lu*exp(-Lu)) * exp(Lu) / S1M;
  Aterm = (Lu/eta) * (1 - (1 + epsth)*(1 + eta/Lu)*exp(-eta)) - K1 - ell/4 - R/2 - LH;
  br = Aterm - (1 + rho)*size - extra;
  if(br <= 0, return(-1));
  return(2*eta^2*ell*br / Lu^2);
};

\\ Mertens route (as in [SZ] Lemma 2 and the Lean proof): total mass sum_{p<=U} log p/p >= L - KM
\\ (Rosser-Schoenfeld: > log x + E - 1/(2 log x), E = -1.332582...), split mass <= e^eta * (ell/4 + delta')/1,
\\ delta' = delta L^2/(eta^2 ell)/2 ...
deltastarM(ell, eta, Lu, H, LH, R, variant) = {
  my(lam = 6.35, logN, tau, B, S1M, rho, size, extra, br, KM);
  KM = 1.332583 + 1/(2*Lu);
  \\ Lemma bias needs s = 1 + eta/Lu in (1, 3/2]
  if(eta/Lu > 1/2, return(-1));
  if(variant == "A", logN = 3*Lu/4, logN = 3*Lu/4 + ell/4);
  tau = (3*exp(logN - Lu) + exp(-Lu)) * (1 + 2*H) / (3*lam*H^(2/3));
  B = 3*lam*H^(-1/3)*exp(Lu)*(1 + tau);
  S1M = exp(Lu) * H^(2/3) / (9*lam^2*(1 + tau + 2*(1 + tau)/B)^2) - 1/2;  \\ (B+2)/(B/(1+tau)) = 1+tau+2(1+tau)/B
  \\ validity: the interpolation count must be a genuine positive size (tiny U gives S1M <= 0, rho < 0)
  if(S1M < 1, return(-1));
  rho = B / S1M;
  if(variant == "A", size = 3*Lu/4 + ell/2 + log(8), size = 3*Lu/4 + ell/4 + log(4.84));
  extra = (THETA_C + 1.5*Lu*exp(-Lu)) * exp(Lu) / S1M;
  br = Lu - KM - exp(eta)*ell/4 - R - LH - (1 + rho)*size - extra;
  if(br <= 0, return(-1));
  return(2*eta^2*ell*br / (exp(eta)*Lu^2));
};

optimize_cM(ell, Hs, LHs, variant) = {
  my(R = Rbound(ell), best = [-1, 0, 0, 0], d, Lu);
  for(i = 1, #Hs,
    forstep(eta = 0.2, 3.0, 0.05,
      forstep(t = 0, 5, 0.03,
        Lu = ell * exp(t);
        d = deltastarM(ell, eta, Lu, Hs[i], LHs[i], R, variant);
        if(d > best[1], best = [d, eta, Lu/ell, Hs[i]]))));
  return(best);
};

\\ ell -> oo: bracket ~ L/4 - b*ell with b = sz + e^eta/4 (sz = 1/2 cube, 1/4 box);
\\ max over L of 2 eta^2 ell (L/4 - b ell)/(e^eta L^2) is at L = 8 b ell and equals eta^2/(32 b e^eta).
asymptotic_cM(variant) = {
  my(sz, best = 0, v, b);
  if(variant == "A", sz = 1/2, sz = 1/4);
  forstep(eta = 0.05, 4, 0.001,
    b = sz + exp(eta)/4;
    v = eta^2 / (32*exp(eta)*b);
    best = max(best, v));
  return(best);
};

\\ maximize over eta, Lu, H
optimize_c(ell, Hs, LHs, K1, variant) = {
  my(R = Rbound(ell), best = [-1, 0, 0, 0], d, Lu, i, eta);
  for(i = 1, #Hs,
    forstep(eta = 0.06, 0.70, 0.02,
      forstep(t = 0, 5, 0.03,
        Lu = ell * exp(t);
        d = deltastar(ell, eta, Lu, Hs[i], LHs[i], K1, R, variant);
        if(d > best[1], best = [d, eta, Lu/ell, Hs[i]]))));
  return(best);
};

\\ asymptotic value (ell -> oo): bracket ~ Lu*(f(eta) - 3/4) - ell*sz,  sz = 3/4 (A) or 1/2 (B)
asymptotic_c(variant) = {
  my(sz, best = 0, eta, a, v);
  if(variant == "A", sz = 3/4, sz = 1/2);
  forstep(eta = 0.01, 0.80, 0.001,
    a = (1 - exp(-eta))/eta - 3/4;
    if(a > 0, v = 2*eta^2*a^2/(4*sz); best = max(best, v)));
  return(best);
};

\\ ---------- class number bound ----------
\\ J-integral constant: (1/2pi) int |zeta(1/2+it)| |3/2+it|^(1/4+eta/2) |Gamma(-1/2+eps+it)| dt
Jconst(eta) = {
  my(f = t -> abs(zeta(1/2 + I*t)) * abs(3/2 + I*t)^(1/4 + eta/2) * abs(gamma(-1/2 + 10^-6 + I*t)));
  return(2 * intnum(t = 0, 60, f(t)) / (2*Pi));
};

\\ lower bound for h(-d) at q = |D| = e^ell given c = c(ell): h >= c*e^(-2c)*(1-err)*sqrt(q)/(pi*ell)
hbound_log(ell, c, Jc) = {
  my(err, eta = 1/ell);
  \\ x = q^2: error term x^(-1/2 + c/ell) * zeta(1+eta) * (q/2pi)^(1/4+eta/2) * Jc
  err = exp(-ell*(1 - 2*c/ell)) * (1 + ell) * exp((ell - log(2*Pi))*(1/4 + eta/2)) * Jc;
  if(err >= 1/2, return(-1e9));
  return(log(c) - 2*c + log(1 - err) + ell/2 - log(Pi) - log(ell));
};

run() = {
  my(ok, K1, Hs, LHs, ells, res, cA, cB, Jc, tab, N, lo, hi, mid, Nlist);
  ok = check_zeta_logder();
  print("zeta log-derivative lemma on grid: ", if(ok, "OK", "FAILED"));
  K1 = compute_K1();
  print("K1 = Euler + sum = ", K1);
  Hs = [10^4, 3*10^4, 10^5, 3*10^5, 10^6, 3*10^6, 10^7, 3*10^7, 10^8];
  LHs = compute_LambdaH(Hs);
  for(i = 1, #Hs, print("H = ", Hs[i], "  Lambda_H = ", LHs[i], "  (log H = ", log(Hs[i]), ")"));
  print("asymptotic c (ell -> oo): variant A = ", asymptotic_c("A"), "   variant B = ", asymptotic_c("B"));
  ells = [log(10^10), log(2^40), 40, 50, 75, 100, 150, 200, 300, 500, 1000, 3000, 10000];
  print("\nell      q          c_A(ell)    [eta, Lu/ell, H]          c_B(ell)    [eta, Lu/ell, H]");
  tab = vector(#ells);
  for(i = 1, #ells,
    cA = optimize_c(ells[i], Hs, LHs, K1, "A");
    cB = optimize_c(ells[i], Hs, LHs, K1, "B");
    tab[i] = [ells[i], cA[1], cB[1]];
    printf("%-8.2f %-10.3e %-11.4e [%.2f, %.2f, %d]   %-11.4e [%.2f, %.2f, %d]\n",
      ells[i], exp(ells[i]), cA[1], cA[2], cA[3], cA[4], cB[1], cB[2], cB[3], cB[4]));
  Jc = Jconst(0.05);
  print("\nJ-integral constant (eta = 0.05 upper estimate): ", Jc);
  \\ discriminant bound D(N): smallest ell0 >= log(10^10) such that h-bound > N for all ell >= ell0.
  \\ c(ell) is taken from variant A / B at ell (increasing in ell; checked in the table).
  Nlist = [100, 200, 500, 1000, 10^4];
  print("\nN      log D_A(N)   D_A(N)        log D_B(N)   D_B(N)");
  for(j = 1, #Nlist,
    N = Nlist[j];
    printf("%-6d %-12.2f %-13.3e %-12.2f %-13.3e\n", N,
      solveD(N, Hs, LHs, K1, Jc, "A"), exp(solveD(N, Hs, LHs, K1, Jc, "A")),
      solveD(N, Hs, LHs, K1, Jc, "B"), exp(solveD(N, Hs, LHs, K1, Jc, "B"))));
  print("\nunconditional tabulation bound 2^40 = ", 2.^40, "  (log = ", log(2.^40), ")");
  print("DONE");
  return(0);
};

\\ bisection on ell for h-bound(ell) = log N, using c(ell) optimized at each ell
solveD(N, Hs, LHs, K1, Jc, variant) = {
  my(lo = log(10^10), hi = 200., mid, c);
  if(hcheck(lo, N, Hs, LHs, K1, Jc, variant), return(lo));
  for(it = 1, 40,
    mid = (lo + hi)/2;
    if(hcheck(mid, N, Hs, LHs, K1, Jc, variant), hi = mid, lo = mid));
  return(hi);
};

hcheck(ell, N, Hs, LHs, K1, Jc, variant) = {
  my(c = optimize_c(ell, Hs, LHs, K1, variant)[1]);
  if(c <= 0, return(0));
  return(hbound_log(ell, c, Jc) > log(N));
};

hcheckM(ell, N, Hs, LHs, Jc, variant) = {
  my(c = optimize_cM(ell, Hs, LHs, variant)[1]);
  if(c <= 0, return(0));
  return(hbound_log(ell, c, Jc) > log(N));
};

solveDM(N, Hs, LHs, Jc, variant) = {
  my(lo = log(10^10), hi = 200., mid);
  if(hcheckM(lo, N, Hs, LHs, Jc, variant), return(lo));
  for(it = 1, 40,
    mid = (lo + hi)/2;
    if(hcheckM(mid, N, Hs, LHs, Jc, variant), hi = mid, lo = mid));
  return(hi);
};

run2() = {
  my(Hs, LHs, ells, cA, cB, Jc, Nlist, N, small);
  print("Mertens route (as in [SZ] Lemma 2 / the Lean proof)");
  Hs = [10^4, 3*10^4, 10^5, 3*10^5, 10^6, 3*10^6, 10^7, 3*10^7, 10^8];
  LHs = compute_LambdaH(Hs);
  print("asymptotic c (ell -> oo): variant A = ", asymptotic_cM("A"), "   variant B = ", asymptotic_cM("B"));
  ells = [log(3), log(10), log(100), log(10^4), log(10^6), log(10^8), log(10^10), log(2^40), 40, 50, 75, 100, 150, 200, 300, 500, 1000, 3000, 10000];
  print("\nell      q          c_A(ell)    [eta, Lu/ell, H]          c_B(ell)    [eta, Lu/ell, H]");
  for(i = 1, #ells,
    cA = optimize_cM(ells[i], Hs, LHs, "A");
    cB = optimize_cM(ells[i], Hs, LHs, "B");
    printf("%-8.2f %-10.3e %-11.4e [%.2f, %.2f, %d]   %-11.4e [%.2f, %.2f, %d]\n",
      ells[i], exp(ells[i]), cA[1], cA[2], cA[3], cA[4], cB[1], cB[2], cB[3], cB[4]));
  Jc = Jconst(0.05);
  Nlist = [100, 200, 500, 1000, 10^4];
  print("\nN      log D_A(N)   D_A(N)        log D_B(N)   D_B(N)");
  for(j = 1, #Nlist,
    N = Nlist[j];
    printf("%-6d %-12.2f %-13.3e %-12.2f %-13.3e\n", N,
      solveDM(N, Hs, LHs, Jc, "A"), exp(solveDM(N, Hs, LHs, Jc, "A")),
      solveDM(N, Hs, LHs, Jc, "B"), exp(solveDM(N, Hs, LHs, Jc, "B"))));
  print("(D values at the floor log(10^10) mean: the bound already holds at d = 10^10)");
  print("DONE");
  return(0);
};

if(type(NO_RUN) != "t_INT", run2());
