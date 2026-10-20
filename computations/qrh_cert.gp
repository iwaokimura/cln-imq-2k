\\ Check of the numbers in the Remark after Theorem 10 of the paper (zero-free half-plane): if no Dirichlet L-function vanishes in
\\ Re s > 31/32, the zero gap (c, T) holds for every c <= T/32, and Proposition 9 with the rational
\\ parameters below gives sqrt(q) L(1, chi) > N pi, i.e. h(-d) > N for log d >= T (by (4) of the paper).
\\ The parameters come from a grid search (rounded); the hypotheses of Proposition 9 are checked exactly,
\\ eps and the lower bound at 100 digits, with relative margins far above the rounding error.
\\ Run: gp -q -f qrh_cert.gp < /dev/null > qrh_cert.txt

if(default(realprecision) < 100, default(realprecision, 100));

check(p) = {
  my(N = p[1], T = p[2], c = p[3], A = p[4], V = p[5], sT, P, eps, lb, ok);
  ok = (c > 0) && (T >= 2) && (c/T <= 1/2) && (c <= T/32) && (A*T >= 3) && (V >= 1) && (V == floor(V));
  sT = 1 - c/T; P = c*(1 + log(2*V*A*T)/T);
  eps = exp(c)*((A*T)^(c/T)*V^(c/T)/(c*A) + 4/(A*T)^sT) + exp(P)/(c*A) + 4*exp(P)/V^sT + exp(P)/(A*T);
  lb = (1 - eps)*c*exp(-P)*exp(T/2)/T;
  printf("N = %d: T = %s, c = %s, A = %d, V = %d; hypotheses %s; eps = %.6f; bound / (N pi) = %.6f; e^T = %.4e (2^40 = %.4e)\n",
         N, T, c, A, V, if(ok, "OK", "FAIL"), eps, lb/(N*Pi), exp(T), 2.^40);
  return(ok && eps < 1 - 10^-6 && lb > N*Pi*(1 + 10^-6));
};

run() = {
  \\ [N, T, c, A, V], all rational
  my(params = [[2000, 272/10, 595/1000, 1000, 1000], [100000, 354/10, 652/1000, 1000, 1000]], all = 1);
  for(i = 1, #params, if(!check(params[i]), all = 0));
  print(if(all, "QRH CERT PASS", "QRH CERT FAIL"));
  return(all);
};

run();
