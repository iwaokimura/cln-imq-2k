\\ (2026-10-09): the certified constant for EXACTLY the statement proved in Lean,
\\ lean/B4ElementaryGap.lean (b4_elementary_zero_gap); cited in the Remark after Proposition 6 of the
\\ paper. It differs from certify_c2.gp (constants of Rosser--Schoenfeld) as follows:
\\   * mode "LEAN": K = 1 + (5 log 2 + 3)/4 + 2/U  (Lean: 1/floor(U) <= 2/U), Theta = log 4,
\\     R = min(ell, log y + log 4 + ell/y) with y = max(ell, 1), LH = log H + log 4,
\\     Z = 2(s-1)/(e s) <= 2 eta/(e Lu), G = 0;
\\   * the side conditions of the Lean theorem:
\\     N = U^(3/4) >= 18818, H <= N, eta <= Lu.
\\ (N is real here; the integer N of the Lean statement is handled in lean_grid.gp.)
\\ Run: gp -q certify_c2_lean.gp < /dev/null > certify_c2_lean.txt

SIDE = 1;
if(type(MODES) != "t_VEC", MODES = ["LEAN"]);
RTAIL = 0;  \\ > 0: use this value for R(ell) in RS mode (tail: log(2 LT))
if(default(parisize) < 400000000, default(parisize, 400000000));
NO_RUN = 1;
read("effective_c2.gp");


\\ Lambda_H: exact table up to 10^8; beyond, RS (3.22) upper bound log x + E + 1/log x (E = -1.332582...)
LHtab(H) = {
  if(H <= 10^8, return(compute_LambdaH([H])[1]));
  return(log(H) - 1.3325822 + 1/log(H));
};

\\ master inequality with the UPSTREAM Lean pivot bounds:
\\   S1/M >= H^(2/3) U / (4*97^2),  S2/S1 <= 192*4*97^2/H
\\ extra term (M theta(U) + M/2 log M)/S1 with log M = 3 Lu
dstarU(ell, eta, Lu, H, LH, mode) = {
  my(U = exp(Lu), S1M, rho, size, extra, br, KM, R, TH, zext = 0);
  if(eta/Lu > 1/2, return(-1));
  if(SIDE && (3*Lu/4 < log(18818) || log(H) > 3*Lu/4), return(-1));
  S1M = H^(2/3) * U / (4*97^2);
  rho = 192*4*97^2 / H;
  size = 3*Lu/4 + ell/2 + log(8);
  if(mode == "RS",
    KM = 1.332583 + 1/(2*Lu); R = if(RTAIL > 0, RTAIL, Rbound(ell)); TH = 1.01624,
    if(mode == "EL",
      KM = 1 + 1.2578 + 2*exp(-Lu); R = min(ell, log(max(ell, 1)) + log(4) + ell/max(ell, 1));
      TH = log(4); zext = exp(eta)*(eta/Lu)/(2*exp(1)),
      KM = 1 + (5*log(2) + 3)/4 + 2*exp(-Lu); R = min(ell, log(max(ell, 1)) + log(4) + ell/max(ell, 1));
      TH = log(4); zext = exp(eta)*(eta/Lu)/exp(1)));
  extra = (TH*U + 3*Lu/2) / S1M;
  br = Lu - KM - exp(eta)*ell/4 - zext - R - LH - (1 + rho)*size - extra;
  if(br <= 0, return(-1));
  return(2*eta^2*ell*br / (exp(eta)*Lu^2));
};


make_grid(LT) = {
  my(g = List(), x = log(3.), l10 = log(10^10), y);
  while(x < LT,
    listput(g, x);
    y = x * if(x >= 23 && x < 46, 1.005, 1.05);
    x = if(x < l10 && y > l10, l10, y));
  listput(g, LT);
  return(Vec(g));
};

certD(N, g, cmin, Jc) = {
  my(n = #g, i0 = n + 1, l10 = log(10^10));
  forstep(i = n - 1, 1, -1,
    if(g[i] < l10, break);
    if(cmin[i] > 0 && hbound_log(g[i], cmin[i], Jc) > log(N), i0 = i, break));
  if(i0 > n - 1, return(-1));
  return(g[i0]);
};


optU(ell, mode, Hs, LHs) = {
  my(best = [-1, 0, 0, 0, 0], d, Lu);
  for(i = 1, #Hs,
    forstep(eta = 0.3, 3.0, 0.05,
      forstep(t = 0, 6, 0.03,
        Lu = ell*exp(t);
        d = dstarU(ell, eta, Lu, Hs[i], LHs[i], mode);
        if(d > best[1], best = [d, eta, Lu/ell, Hs[i], LHs[i]]))));
  return(best);
};

\\ the bracket is nonincreasing in ell for fixed (eta, Lu, H): R, e^eta ell/4 and size grow; rho and the
\\ extra term do not depend on ell. Rbound and the elementary R are nondecreasing in ell.
cert_intervalU(l0, l1, mode, Hs, LHs) = {
  my(opt = optU(l0, mode, Hs, LHs));
  if(opt[1] <= 0, return(-1));
  return(dstarU(l1, opt[2], opt[3]*l0, opt[4], opt[5], mode) * l0 / l1);
};

run5() = {
  my(Hs = [10^8, 10^9, 10^10, 10^11, 10^12], LHs, g, LT = 10000., n, c, minc, Jc, Nlist = [100, 200, 500, 1000], d, mode, i10);
  g = make_grid(LT); n = #g;
  Jc = Jconst(0.05);
  foreach(MODES, mode,
    LHs = vector(#Hs, i, if(mode == "RS", LHtab(Hs[i]), log(Hs[i]) + log(4)));
    print("\n=== mode ", mode, " ===");
    c = vector(n);
    for(i = 1, n - 1, c[i] = cert_intervalU(g[i], g[i+1], mode, Hs, LHs));
    \\ tail: with Lu = t ell every term of br/ell is nondecreasing (R(ell) <= log(2 ell) in RS mode, as in
    \\ certify_c2.gp; R_el(ell)/ell decreases); value at LT is a lower bound
    if(mode == "RS", RTAIL = log(2*LT));
    c[n] = optU(LT, mode, Hs, LHs)[1];
    RTAIL = 0;
    print("tail ell >= ", LT, ": c >= ", c[n]);
    minc = c;
    forstep(i = n - 1, 1, -1, minc[i] = min(c[i], minc[i+1]));
    print("certified for all ell >= log 3:  c >= ", minc[1]);
    i10 = select(i -> g[i+1] > log(10^10), [1..n-1])[1];
    print("certified for ell >= log 10^10: c >= ", minc[i10]);
    print("N      D(N)");
    for(j = 1, #Nlist,
      d = certD(Nlist[j], g, minc, Jc);
      printf("%-6d %-16.3e\n", Nlist[j], if(d > 0, exp(d), -1))));
  print("LEAN DONE");
  return(0);
};

if(type(NO_RUN5) != "t_INT", run5());
