\\ (2026-10-10): parameters for the Lean interval certificates.
\\ For each l-interval [l0, l1], choose N = 2^k, H = 2^(3j), eta = a/20 and the ramified bound
\\ Rb = l1 (ropt = 0) or Rb = (m+2) log 2 + l1/2^m (ropt = 1, y = 2^m), and evaluate EXACTLY the closed
\\ form cval of lean/B4Interval.lean (interval_gap):
\\   L    = 4/3 k log 2
\\   br   = L - (1 + (5 log 2 + 3)/4 + 1/1000) - e^eta (l1/4 + eta e^-1 / L) - Rb - (3j + 2) log 2
\\          - (1 + 192*4*97^2/2^(3j)) ((k + 3) log 2 + l1/2) - 4*97^2 (2 log 2 + 1/1000)/4^j
\\   cval = 2 eta^2 l0 e^-eta / L^2 * br
\\ Side conditions of interval_gap: k >= 15, 1 <= j, 3j <= k, 0 < eta <= 13, 0 < l0 <= l1, br >= 0.
\\ The target c_i written to the Lean file is cval rounded DOWN to 4 significant digits.
\\ Output: the table (stdout), the Lean certificate file LEANOUT, and DATAOUT (grid and minc as GP data;
\\ not used by the other scripts here).
\\ Run: gp -q lean_grid.gp < /dev/null > lean_grid.txt

if(default(parisize) < 400000000, default(parisize, 400000000));
NO_RUN = 1;
read("effective_c2.gp");
if(type(LEANOUT) != "t_STR", LEANOUT = "../lean/B4Certificates.lean");
if(type(LT) != "t_REAL" && type(LT) != "t_INT", LT = 10000);
if(type(DATAOUT) != "t_STR", DATAOUT = "lean_grid_c.gp");

LG2 = log(2.);

brval(k, j, m, ropt, eta, l1) = {
  my(L = 4/3*k*LG2, Rb);
  Rb = if(ropt == 0, l1, (m + 2)*LG2 + l1/2^m);
  return(L - (1 + (5*LG2 + 3)/4 + 1/1000) - exp(eta)*(l1/4 + eta*exp(-1)/L) - Rb - (3*j + 2)*LG2
    - (1 + 192*4*97^2/2^(3*j))*((k + 3)*LG2 + l1/2) - 4*97^2*(2*LG2 + 1/1000)/4^j);
};

cval(k, j, m, ropt, a, l0, l1) = {
  my(eta = a/20, L = 4/3*k*LG2, br);
  if(k < 15 || j < 1 || 3*j > k || a < 1 || eta > 13, return(-1));
  br = brval(k, j, m, ropt, eta, l1);
  if(br < 0, return(-1));
  return(2*eta^2*l0*exp(-eta)/L^2 * br);
};

\\ tail (l >= T): c_T = 2 eta^2 e^-eta (alpha - C0/T)/(a + b/T)^2, as in lean/B4Chain.lean (tail_gap)
tailval(j, m, tau, eta, T) = {
  my(a = 4/3*tau*LG2, b = 4/3*LG2, rho = 192*4*97^2/2^(3*j), al, C0);
  if(tau*T < 15 + 3*j || a < 1 || eta > 13, return(-1));
  al = a - exp(eta)/4 - 1/2^m - (1 + rho)*(tau*LG2 + 1/2);
  C0 = (1 + (5*LG2 + 3)/4 + 1/1000) + exp(eta)*eta*exp(-1)/T + (m + 2)*LG2 + (3*j + 2)*LG2
    + 4*(1 + rho)*LG2 + 4*97^2*(2*LG2 + 1/1000)/4^j;
  return(2*eta^2*exp(-eta)*(al - C0/T)/(a + b/T)^2);
};

besttail(T) = {
  my(best = [-1, 0, 0, 0, 0], v);
  for(j = 1, 20, for(m = 10, 24, forstep(tp = 200, 3000, 20, for(a = 4, 60,
    v = tailval(j, m, tp/100, a/20, T);
    if(v > best[1], best = [v, j, m, tp, a])))));
  \\ refine tau
  for(tp = 10*best[4] - 200, 10*best[4] + 200, for(a = best[5] - 2, best[5] + 2,
    v = tailval(best[2], best[3], tp/1000, a/20, T);
    if(v > best[1], best = [v, best[2], best[3], tp/10, a])));
  return(best);
};

\\ best Rb: ropt = 0 or the best m
bestR(l1) = {
  my(best = [0, 0, l1], v);
  for(m = 0, 24, v = (m + 2)*LG2 + l1/2^m; if(v < best[3], best = [1, m, v]));
  return(best);
};

\\ best (a, j) for fixed k
bestAJ(k, l0, l1, rr) = {
  my(best = [-1, 0, 0], v);
  for(j = 1, min(30, k\3),
    for(a = 2, 70,
      v = cval(k, j, rr[2], rr[1], a, l0, l1);
      if(v > best[1], best = [v, a, j])));
  return(best);
};

\\ coordinate search over k
bestK(k0, l0, l1, rr) = {
  my(k = max(15, k0), cur = bestAJ(max(15, k0), l0, l1, rr), steps = [0.3, 0.1, 0.03, 0.01, 0.003, 0], kk, v, moved);
  for(s = 1, #steps,
    moved = 1;
    while(moved,
      moved = 0;
      foreach([-1, 1], sg,
        kk = if(steps[s] == 0, k + sg, round(k*(1 + sg*steps[s])));
        if(kk >= 15 && kk != k,
          v = bestAJ(kk, l0, l1, rr);
          if(v[1] > cur[1], cur = v; k = kk; moved = 1)))));
  return([cur[1], k, cur[3], cur[2]]);
};

\\ rational grid: first point 10986/10000 <= log 3, ratio as in certify_c2.gp, rounded to 4 decimals
make_qgrid(LT) = {
  my(g = List(), x = 10986/10000, l10 = log(10^10), y);
  while(x < LT,
    listput(g, x);
    y = x * if(x >= 23 && x < 46, 1.005, 1.05);
    if(x < l10 && y > l10, y = l10);
    x = ceil(y*10^4)/10^4);
  listput(g, LT);
  return(Vec(g));
};

rounddown4(v) = {
  my(e = floor(log(v)/log(10)) - 3);
  return(floor(v/10^e)*10^e);
};

run() = {
  my(g = make_qgrid(LT), n, res, k0 = 263, rr, r, c, minc, Jc, Nlist = [100, 200, 500, 1000, 2000], d, i10, fd, tl, tct, Dl, Rb, args, targs);
  n = #g;
  res = vector(n - 1);
  for(i = 1, n - 1,
    rr = bestR(g[i+1]);
    r = bestK(k0, g[i], g[i+1], rr);
    k0 = r[2];
    res[i] = [g[i], g[i+1], r[2], r[3], r[4], rr[1], rr[2], r[1], rounddown4(r[1])]);
  print("i  l0  l1  k  j  a  ropt  m  cval  c_target");
  for(i = 1, n - 1, print(i, "  ", res[i]));
  tl = besttail(LT);
  tct = rounddown4(tl[1]);
  print("tail l >= ", LT, ": j ", tl[2], " m ", tl[3], " tau ", tl[4]/100, " eta ", tl[5], "/20  c_T ", tl[1], "  target ", tct);
  c = vector(n, i, if(i < n, res[i][9], tct));
  minc = c;
  forstep(i = n - 1, 1, -1, minc[i] = min(c[i], minc[i+1]));
  print("certified (Lean grid) for all l >= 1.0986: c >= ", minc[1]);
  i10 = select(i -> g[i+1] > log(10^10), [1..n-1])[1];
  print("for l >= log 10^10: c >= ", minc[i10]);
  Jc = Jconst(0.05);
  print("N      D(N)    l_i    minc_i   chain index");
  Dl = vector(#Nlist);
  for(jj = 1, #Nlist,
    d = certD(Nlist[jj], g, minc, Jc);
    Dl[jj] = if(d > 0, select(i -> g[i] == d, [1..n])[1], 0);
    printf("%-6d %-12.4e %-10s %s  %d\n", Nlist[jj], if(d > 0, exp(d), -1), d, if(d > 0, minc[Dl[jj]], -1), Dl[jj]));
  \\ the Lean certificate file
  fd = fileopen(LEANOUT, "w");
  filewrite(fd, "/-\nB-4 (iii): LeanCert certificates and the chain. GENERATED by computations/lean_grid.gp; do not edit.\n`cert_i`: the closed inequality on [l_i, l_{i+1}]; `gap_i : GapOn c_i l_i l_{i+1}`;\n`chain_i : GapFrom minc_i l_i` (minc_i = min of c_j, j >= i, and the tail);\n`tail : GapFrom c_T T` (tail_gap).\n-/");
  filewrite(fd, "import B4Chain\nimport LeanCert.Tactic\n\nnamespace B4.Cert\n\nset_option maxHeartbeats 4000000\nset_option linter.unusedSimpArgs false\n");
  for(i = 1, n - 1,
    r = res[i];
    Rb = if(r[6] == 0, Str("(", r[2], " : ℝ)"), Str("((", r[7] + 2, " : ℝ) * Real.log 2 + (", r[2], " : ℝ) / ", 2^r[7], ")"));
    args = Str("((", r[3], " : ℕ) : ℝ) ((", r[4], " : ℕ) : ℝ) (", 2^(3*r[4]), " : ℝ) (", 4^r[4], " : ℝ) ", Rb,
      " (", r[5], "/20 : ℝ) (", r[1], " : ℝ) (", r[2], " : ℝ) (", r[9], " : ℝ)");
    filewrite(fd, Str("theorem cert_", i, " : B4.certProp ", args, " := by"));
    filewrite(fd, "  simp only [B4.certProp, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]; leancert (trust := kernel)\n");
    filewrite(fd, Str("theorem gap_", i, " : B4.GapOn (", r[9], " : ℝ) (", r[1], " : ℝ) (", r[2], " : ℝ) :="));
    filewrite(fd, Str("  B4.gapOn_of_cert ", r[3], " ", r[4], " ", r[7], " (by norm_num) (by norm_num) (by norm_num) (", r[5], "/20 : ℝ) (", r[1], " : ℝ) (", r[2], " : ℝ) ", Rb, " (", r[9], " : ℝ)"));
    filewrite(fd, Str("    (by norm_num) (by norm_num) (by norm_num) ", if(r[6] == 0, "(Or.inl le_rfl)", "(Or.inr (by norm_num))"), " (", 2^(3*r[4]), " : ℝ) (", 4^r[4], " : ℝ) (by norm_num) (by norm_num) (by norm_num) cert_", i, "\n")));
  targs = Str("((", tl[2], " : ℕ) : ℝ) ((", tl[3], " : ℕ) : ℝ) (", 2^tl[3], " : ℝ) (", 2^(3*tl[2]), " : ℝ) (", 4^tl[2], " : ℝ) (", tl[4], "/100 : ℝ) (", tl[5], "/20 : ℝ) (", LT, " : ℝ) (", tct, " : ℝ)");
  filewrite(fd, Str("theorem cert_tail : B4.certTail ", targs, " := by"));
  filewrite(fd, "  simp only [B4.certTail, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]; leancert (trust := kernel)\n");
  filewrite(fd, Str("theorem tail : B4.GapFrom (", tct, " : ℝ) (", LT, " : ℝ) :="));
  filewrite(fd, Str("  B4.tail_gap ", tl[2], " ", tl[3], " (by norm_num) (", tl[4], "/100 : ℝ) (", tl[5], "/20 : ℝ) (", LT, " : ℝ) (", tct, " : ℝ)"));
  filewrite(fd, Str("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by nlinarith [Real.log_two_gt_d9])"));
  filewrite(fd, Str("    (", 2^tl[3], " : ℝ) (", 2^(3*tl[2]), " : ℝ) (", 4^tl[2], " : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) cert_tail\n"));
  forstep(i = n - 1, 1, -1,
    filewrite(fd, Str("theorem chain_", i, " : B4.GapFrom (", minc[i], " : ℝ) (", g[i], " : ℝ) :="));
    filewrite(fd, Str("  B4.gapFrom_join gap_", i, " ", if(i == n - 1, "tail", Str("chain_", i + 1)), " (by norm_num) (by norm_num)\n")));
  filewrite(fd, Str("theorem log_three_ge : (", g[1], " : ℝ) ≤ Real.log 3 := by leancert (trust := kernel)\n"));
  filewrite(fd, "/-- **Explicit zero gap, all q ≥ 3, q ≠ 8** (elementary inputs, upstream counting). -/");
  filewrite(fd, "theorem zero_gap_all (q : ℕ) [NeZero q] (hq : 3 ≤ q) (hq8 : q ≠ 8) (χ : DirichletCharacter ℂ q)");
  filewrite(fd, "    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (β : ℝ) (hβ0 : 0 < β)");
  filewrite(fd, Str("    (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :\n    (", minc[1], " : ℝ) ≤ (1 - β) * Real.log q :="));
  filewrite(fd, "  chain_1 q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero\n    (log_three_ge.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hq)))\n");
  for(jj = 1, #Nlist,
    if(Dl[jj] > 0,
      filewrite(fd, Str("-- class numbers h ≤ ", Nlist[jj], ": D = exp(l) = ", exp(g[Dl[jj]])));
      filewrite(fd, Str("theorem zero_gap_for_h", Nlist[jj], " : B4.GapFrom (", minc[Dl[jj]], " : ℝ) (", g[Dl[jj]], " : ℝ) := chain_", Dl[jj], "\n"))));
  filewrite(fd, "#print axioms zero_gap_all\n#print axioms zero_gap_for_h1000\n#print axioms zero_gap_for_h2000\n\nend B4.Cert");
  fileclose(fd);
  \\ data for elem_L1.gp: the grid and the Lean-certified minc
  fd = fileopen(DATAOUT, "w");
  filewrite(fd, Str("LG_g = ", g, ";"));
  filewrite(fd, Str("LG_minc = ", minc, ";"));
  fileclose(fd);
  print("LEAN GRID DONE");
  return(0);
};

certD(N, g, cmin, Jc) = {
  my(n = #g, i0 = n + 1, l10 = log(10^10));
  forstep(i = n - 1, 1, -1,
    if(g[i] < l10, break);
    if(cmin[i] > 0 && hbound_log(g[i], cmin[i], Jc) > log(N), i0 = i, break));
  if(i0 > n - 1, return(-1));
  return(g[i0]);
};

if(type(NO_RUN_GRID) != "t_INT", run());
