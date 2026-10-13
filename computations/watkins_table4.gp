\\ Regression test: recompute Watkins' Table 4 (Math. Comp. 73 (2004), p. 936):
\\ for each N <= 100, the number of fundamental discriminants -d with h(-d) = N and the largest d.
\\ We compute h(-d) with qfbclassno for all fundamental -d with d <= DMAX and compare with the
\\ table as transcribed from the paper. (Completeness beyond DMAX is Watkins' theorem.)
\\ Run: gp -q watkins_table4.gp < /dev/null > watkins_table4.txt

if(default(parisize) < 200000000, default(parisize, 200000000));

\\ [N, count, largest d], transcribed from Watkins, Table 4
watkins_table() = {
  return([
  [1,9,163],[2,18,427],[3,16,907],[4,54,1555],[5,25,2683],[6,51,3763],[7,31,5923],[8,131,6307],
  [9,34,10627],[10,87,13843],[11,41,15667],[12,206,17803],[13,37,20563],[14,95,30067],[15,68,34483],
  [16,322,31243],[17,45,37123],[18,150,48427],[19,47,38707],[20,350,58507],
  [21,85,61483],[22,139,85507],[23,68,90787],[24,511,111763],[25,95,93307],[26,190,103027],
  [27,93,103387],[28,457,126043],[29,83,166147],[30,255,134467],[31,73,133387],[32,708,164803],
  [33,101,222643],[34,219,189883],[35,103,210907],[36,668,217627],[37,85,158923],[38,237,289963],
  [39,115,253507],[40,912,260947],
  [41,109,296587],[42,339,280267],[43,106,300787],[44,691,319867],[45,154,308323],[46,268,462883],
  [47,107,375523],[48,1365,335203],[49,132,393187],[50,345,389467],[51,159,546067],[52,770,439147],
  [53,114,425107],[54,427,532123],[55,163,452083],[56,1205,494323],[57,179,615883],[58,291,586987],
  [59,128,474307],[60,1302,662803],
  [61,132,606643],[62,323,647707],[63,216,991027],[64,1672,693067],[65,164,703123],[66,530,958483],
  [67,120,652723],[68,976,819163],[69,209,888427],[70,560,811507],[71,150,909547],[72,1930,947923],
  [73,119,886867],[74,407,951043],[75,237,916507],[76,1075,1086187],[77,216,1242763],[78,561,1004347],
  [79,175,1333963],[80,2277,1165483],
  [81,228,1030723],[82,402,1446547],[83,150,1074907],[84,1715,1225387],[85,221,1285747],[86,472,1534723],
  [87,222,1261747],[88,1905,1265587],[89,192,1429387],[90,801,1548523],[91,214,1391083],[92,1248,1452067],
  [93,262,1475203],[94,509,1587763],[95,241,1659067],[96,3283,1684027],[97,185,1842523],[98,580,2383747],
  [99,289,1480627],[100,1736,1856563]]);
};

compute_counts(DMAX) = {
  my(cnt = vector(100), big = vector(100), h, nf = 0, fl = fileopen("watkins_h100_list.txt", "w"));
  for(d = 3, DMAX,
    if(isfundamental(-d),
      nf++;
      h = qfbclassno(-d);
      if(h <= 100, cnt[h]++; big[h] = d; filewrite(fl, Str(d, " ", h)))));
  fileclose(fl);
  print("fundamental discriminants -d with d <= ", DMAX, ": ", nf);
  return([cnt, big]);
};

run() = {
  my(T = watkins_table(), DMAX = 2500000, res, cnt, big, bad = 0, out, fd);
  res = compute_counts(DMAX); cnt = res[1]; big = res[2];
  fd = fileopen("watkins_table4_computed.txt", "w");
  for(N = 1, 100, filewrite(fd, Str(N, " ", cnt[N], " ", big[N])));
  fileclose(fd);
  for(i = 1, #T,
    if(cnt[T[i][1]] != T[i][2] || big[T[i][1]] != T[i][3],
      bad++;
      print("MISMATCH N = ", T[i][1], ": Watkins ", T[i][2], " ", T[i][3], " | computed ", cnt[T[i][1]], " ", big[T[i][1]])));
  print("compared ", #T, " rows; mismatches: ", bad);
  print(if(bad == 0, "REGRESSION OK", "REGRESSION FAILED"));
  return(bad);
};

run();
