\\ Certified lower bounds for the Mertens-route constant (see effective_c2.gp), with the constants of
\\ Rosser--Schoenfeld; cited in the Remark after Proposition 6 of the paper.
\\ For fixed (eta, L = log U, H) the bracket br(ell) in deltastarM is nonincreasing in ell
\\ (R(ell), e^eta*ell/4, size and, in variant B, rho and the extra term all grow with ell).
\\ Hence on [l0, l1]:  delta*(ell) >= 2 eta^2 l0 br(l1) / (e^eta L^2) = deltastarM(l1, ...) * l0/l1.
\\ Tail ell >= LT: with L = t*ell, br(ell)/ell is nondecreasing once R(ell) is replaced by log(2 ell),
\\ so delta*(ell) >= deltastarM(LT, eta, t*LT, H, LH, log(2 LT)).
\\ Run: gp -q certify_c2.gp < /dev/null > certify_c2.txt

if(default(parisize) < 400000000, default(parisize, 400000000));
NO_RUN = 1;
read("effective_c2.gp");

\\ grid of ell: ratio 1.05, refined to 1.005 on [23, 46] where D(N) is decided
make_grid(LT) = {
  my(g = List(), x = log(3.), l10 = log(10^10), y);
  while(x < LT,
    listput(g, x);
    y = x * if(x >= 23 && x < 46, 1.005, 1.05);
    \\ log 10^10 is a grid point, so the bound for q >= 10^10 starts there (2026-10-09, found by an independent recheck)
    x = if(x < l10 && y > l10, l10, y));
  listput(g, LT);
  return(Vec(g));
};

\\ certified value on [l0, l1], parameters optimized at l0 with L held fixed
cert_interval(l0, l1, Hs, LHs, variant) = {
  my(opt = optimize_cM(l0, Hs, LHs, variant), L, j, v);
  if(opt[1] <= 0, return([-1, 0, 0, 0]));
  L = opt[3] * l0;
  j = 1; while(Hs[j] != opt[4], j++);
  v = deltastarM(l1, opt[2], L, Hs[j], LHs[j], Rbound(l1), variant) * l0 / l1;
  return([v, opt[2], opt[3], opt[4]]);
};

cert_tail(LT, Hs, LHs, variant) = {
  my(opt = optimize_cM(LT, Hs, LHs, variant), j);
  j = 1; while(Hs[j] != opt[4], j++);
  if(Rbound(LT) > log(2*LT), error("R(LT) > log(2 LT)"));
  return(deltastarM(LT, opt[2], opt[3]*LT, Hs[j], LHs[j], log(2*LT), variant));
};

\\ D(N): smallest grid point ell_i >= log(10^10) such that for every j >= i the h-bound with
\\ (ell_j, min of certified c on [ell_j, oo)) exceeds log N. hbound_log increases in ell and in c (c < 1/2).
certD(N, g, cmin, Jc) = {
  my(n = #g, i0 = n + 1, l10 = log(10^10));
  forstep(i = n - 1, 1, -1,
    if(g[i] < l10, break);
    if(cmin[i] > 0 && hbound_log(g[i], cmin[i], Jc) > log(N), i0 = i, break));
  if(i0 > n - 1, return(-1));
  return(g[i0]);
};

run3() = {
  my(Hs, LHs, g, LT = 10000., n, cA, cB, minA, minB, tA, tB, Jc, Nlist, dA, dB, fd);
  Hs = [10^4, 3*10^4, 10^5, 3*10^5, 10^6, 3*10^6, 10^7, 3*10^7, 10^8];
  LHs = compute_LambdaH(Hs);
  g = make_grid(LT); n = #g;
  print("grid points: ", n);
  cA = vector(n); cB = vector(n);
  for(i = 1, n - 1,
    cA[i] = cert_interval(g[i], g[i+1], Hs, LHs, "A")[1];
    cB[i] = cert_interval(g[i], g[i+1], Hs, LHs, "B")[1]);
  tA = cert_tail(LT, Hs, LHs, "A"); tB = cert_tail(LT, Hs, LHs, "B");
  cA[n] = tA; cB[n] = tB;
  print("tail ell >= ", LT, ": c_A >= ", tA, "   c_B >= ", tB);
  \\ suffix minima: certified c on [g[i], oo)
  minA = cA; minB = cB;
  forstep(i = n - 1, 1, -1, minA[i] = min(cA[i], minA[i+1]); minB[i] = min(cB[i], minB[i+1]));
  print("certified for all ell >= log 3:  c_A >= ", minA[1], "   c_B >= ", minB[1]);
  \\ the interval containing log 10^10 counts too (corrected 2026-10-09 after an independent recheck: was g[i] >= log 10^10)
  print("certified for ell >= log 10^10: c_A >= ", minA[select(i -> g[i+1] > log(10^10), [1..n-1])[1]],
        "   c_B >= ", minB[select(i -> g[i+1] > log(10^10), [1..n-1])[1]]);
  print("\ninterval [ell_i, ell_i+1]   c_A (certified)   c_B (certified)   (every 10th row)");
  forstep(i = 1, n - 1, 10, printf("%-9.3f %-9.3f   %-12.4e   %-12.4e\n", g[i], g[i+1], cA[i], cB[i]));
  Jc = Jconst(0.05);
  Nlist = [100, 200, 500, 1000, 10^4];
  print("\nN      D_A(N) certified     D_B(N) certified");
  for(k = 1, #Nlist,
    dA = certD(Nlist[k], g, minA, Jc); dB = certD(Nlist[k], g, minB, Jc);
    printf("%-6d %-20.3e %-20.3e\n", Nlist[k], if(dA > 0, exp(dA), -1), if(dB > 0, exp(dB), -1)));
  print("CERTIFY DONE");
  return(0);
};

run3();
