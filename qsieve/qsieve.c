/*
 * qsieve: Watkins-style minima sieve certifying h(-d) > N for fundamental discriminants -d,
 * d in [lo, hi]  (Watkins, Math. Comp. 73 (2004), Sect. 8; our notes: watkins-plan.tex).
 *
 * Certification (sound, lower bound): the number of reduced forms equals h(-d), and by Watkins'
 * Lemma 3 the minima <= X = sqrt(d/4) are multiplicative: a split prime p (chi(p)=+1) gives p^l
 * twice for every p^l <= X, a ramified prime p <= X gives p once, coprime products multiply.
 * We count weighted products n <= X (n = 1 included) built from known split/ramified primes.
 *
 * Phase 1 (class mode, segments of length >= Q): classes r mod Q = 16*9*5*...*29 determine the
 *   symbols of all primes <= 29.  For each dyadic segment [2^k, 2^(k+1)) we precompute, per symbol
 *   pattern, the number s of "sieving sets" (35 consecutive primes from 31) that must each contain
 *   a split prime; worst case: that prime is the largest of its set (Watkins).  s = 0: the whole
 *   class is certified and skipped.
 * Phase 2: for d in an uncertified class, check sets 1..s for a split prime.
 * Phase 2b: closed-form bound h >= W0 (2k^2+1) from split primes in the sieving-set table.
 * Phase 3 (rare): exact count with all split/ramified primes up to min(X, PEXACT).
 * Anything still uncertified is written to residual.<w>.txt; a GP script (postproc.gp) checks
 *   fundamentality and computes h(-d) for those d.
 * Short segments (< Q) use direct mode: every d is handled individually by phases 2-3.
 * Bit-parallel class mask (classes with >= K_min values of d): per set, OR of the shifted periodic
 *   split-patterns of its 35 primes, AND over the sets.  Offsets are computed without division
 *   (Barrett / Lemire fastmod); for W <= 16 words the masks stay in AVX-512 (or AVX2) registers.
 *   -M selects the original or the division-free scalar version for cross-checking; -V tests all three.
 *
 * Parallelism: process level (fork).  Work units are (segment, residue mod 23*29) chunks in class
 * mode and subranges in direct mode, assigned round robin to workers.  Each worker appends a
 * progress line to log.<w>.txt every interval seconds (default 1200), with an ETA.
 *
 * Usage: qsieve -N 200 -a LO -b HI [-j 12] [-i 1200] [-o outdir]
 * All arithmetic fits in 64 bits for hi < 2^63.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#if defined(__AVX2__) || defined(__AVX512F__)
#include <immintrin.h>
#endif

typedef unsigned long long u64;
typedef __int128 i128;

#define NSMALL 10
static const int SP[NSMALL] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29};
static const int CM[NSMALL] = {16, 9, 5, 7, 11, 13, 17, 19, 23, 29};
#define Q 155272637520ULL
#define NPAT 59049 /* 3^10 */
#define SETSIZE 35
#define SMAX 40
#define PEXACT 2000000

static int N;
static int check_bound = 0; /* -C: verify every bound certification by the exact count */
static int scalar_only = 0; /* -S: disable the bit-parallel class sieve (for cross-checking) */
static long long kmin_bp = 10; /* -K: use bit-parallel sieving for classes with at least this many d (measured 2026-10-09) */
static long long n_bound_bad;
static int mask_impl = 0; /* -M: 0 auto (SIMD), 1 original, 2 division-free scalar (for cross-checking) */
static int max_chunk = -1; /* -U: process only class-mode chunks < this (benchmarking only) */
static int force_all = 0; /* test option -T: treat every class as uncertified (need >= 1) */
static int nprimes;
static int *primes;          /* all primes < PEXACT */
static int setp[SMAX][SETSIZE];
static int vmax[SMAX];       /* largest prime of each set */
static signed char *legtab[SMAX][SETSIZE]; /* legtab[j][i][r] = (-r | p) for p = setp[j][i] */
static u64 cmE[NSMALL];      /* CRT idempotents for the component moduli */
#define NTAB (SMAX * SETSIZE)
static int tabp[NTAB];             /* sieving-set primes 31.. in increasing order */
static signed char *tabl[NTAB];    /* tabl[t][r] = (-r | tabp[t]) */
/* closed-form bound (phase 2b): thresholds = number of table primes used */
#define NTHR 9
static const int THRN[NTHR] = {8, 16, 32, 64, 128, 256, 512, 1024, NTAB};
static int compsym[NSMALL][32]; /* rows indexed by d mod CM[i], CM[i] <= 29 */ /* symbol (-d | p) given d mod CM[i] */

/* ---------- utilities ---------- */
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + 1e-9 * t.tv_nsec;
}

static u64 isqrt64(u64 x) {
  u64 r = (u64)sqrtl((long double)x);
  while (r * r > x) r--;
  while ((r + 1) * (r + 1) <= x) r++;
  return r;
}

static int jacobi(long long a, long long n) { /* n odd positive */
  int t = 1;
  a %= n;
  if (a < 0) a += n;
  while (a) {
    while ((a & 1) == 0) {
      a >>= 1;
      long long r = n & 7;
      if (r == 3 || r == 5) t = -t;
    }
    long long tmp = a; a = n; n = tmp;
    if ((a & 3) == 3 && (n & 3) == 3) t = -t;
    a %= n;
  }
  return n == 1 ? t : 0;
}

/* Kronecker symbol (-d | p) for prime p */
static int kron_minus_d(u64 d, int p) {
  if (p == 2) {
    int r = (int)(d & 7);
    if ((d & 1) == 0) return 0;
    /* -d mod 8: d=7 -> 1 (+1), d=1 -> 7 (+1), d=3 -> 5 (-1), d=5 -> 3 (-1) */
    return (r == 7 || r == 1) ? 1 : -1;
  }
  u64 r = d % (u64)p;
  if (r == 0) return 0;
  return jacobi((long long)(p - r), p);
}

/* ---------- minima counting ---------- */
/* weighted count of n <= X from primes P[0..np-1] (sorted), sp[i]=1 split, 0 ramified; capped */
typedef struct { u64 n; long long w; int idx; } frame;
static frame *stk;
static long long count_min(const u64 *P, const char *sp, int np, u64 X, long long cap) {
  int top = 0;
  long long total = 0;
  stk[top++] = (frame){1, 1, 0};
  while (top > 0) {
    frame e = stk[--top];
    total += e.w;
    if (total >= cap) return cap;
    for (int i = e.idx; i < np; i++) {
      u64 p = P[i];
      if ((i128)e.n * p > (i128)X) break;
      if (sp[i]) {
        u64 m = e.n * p;
        while (m <= X) {
          stk[top++] = (frame){m, 2 * e.w, i + 1};
          if ((i128)m * p > (i128)X) break;
          m *= p;
        }
      } else {
        stk[top++] = (frame){e.n * p, e.w, i + 1};
      }
      if (top > 4000000) return cap; /* safety: count already huge */
    }
  }
  return total;
}

/* ---------- precomputation ---------- */
static void init_primes(void) {
  char *c = calloc(PEXACT, 1);
  primes = malloc(sizeof(int) * 200000);
  nprimes = 0;
  for (int i = 2; i < PEXACT; i++) {
    if (!c[i]) {
      primes[nprimes++] = i;
      for (long long j = (long long)i * i; j < PEXACT; j += i) c[j] = 1;
    }
  }
  free(c);
  int k = 0;
  while (primes[k] < 31) k++;
  for (int j = 0; j < SMAX; j++) {
    for (int i = 0; i < SETSIZE; i++) {
      int p = primes[k++];
      setp[j][i] = p;
      legtab[j][i] = malloc(p);
      for (int r = 0; r < p; r++) legtab[j][i][r] = (signed char)(r == 0 ? 0 : jacobi(p - r, p));
      tabp[j * SETSIZE + i] = p;
      tabl[j * SETSIZE + i] = legtab[j][i];
    }
    vmax[j] = setp[j][SETSIZE - 1];
  }
  /* CRT idempotents and component symbols */
  for (int i = 0; i < NSMALL; i++) {
    u64 m = CM[i], M = Q / m, inv = 0;
    for (u64 t = 1; t < m; t++)
      if ((M % m) * t % m == 1) { inv = t; break; }
    cmE[i] = (u64)(((i128)M * inv) % Q);
    for (int r = 0; r < CM[i]; r++) {
      int s;
      if (SP[i] == 2) {
        if (r == 3 || r == 11) s = -1;
        else if (r == 7 || r == 15) s = 1;
        else if (r == 4 || r == 8) s = 0;
        else s = 9; /* not a fundamental-discriminant class */
      } else if (SP[i] == 3) {
        if (r == 0) s = 9;
        else if (r % 3 == 0) s = 0;
        else s = (r % 3 == 2) ? 1 : -1; /* (-d|3): d=2 mod 3 -> -d=1 -> +1 */
      } else {
        s = (r == 0) ? 0 : jacobi(SP[i] - r, SP[i]);
      }
      compsym[i][r] = s;
    }
  }
  stk = malloc(sizeof(frame) * 4000064);
}

/* W0[pat*NTHR+t] = weighted count of pattern products m <= X / B_t^2, B_t = tabp[THRN[t]-1] (cap N+1) */
static unsigned short *W0;

/* s_needed[pat] for X: 0 certified by small primes; 1..SMAX sets; SMAX+1 never (exact pass) */
static void build_pattern_table(unsigned char *sneed, u64 X) {
  u64 P[NSMALL + SMAX];
  char spf[NSMALL + SMAX];
  for (int pat = 0; pat < NPAT; pat++) {
    int t = pat, np = 0;
    for (int i = 0; i < NSMALL; i++) {
      int s = t % 3 - 1;
      t /= 3;
      if (s == 1) { P[np] = SP[i]; spf[np++] = 1; }
      else if (s == 0 && (u64)SP[i] <= X) { P[np] = SP[i]; spf[np++] = 0; }
    }
    for (int k = 0; k < SMAX; k++) { P[np + k] = vmax[k]; spf[np + k] = 1; }
    int need;
    if (count_min(P, spf, np, X, N + 1) > N) need = 0;
    else if (count_min(P, spf, np + SMAX, X, N + 1) <= N) need = SMAX + 1;
    else { /* smallest k in [1, SMAX] with count > N */
      int a = 1, b = SMAX;
      while (a < b) {
        int m = (a + b) / 2;
        if (count_min(P, spf, np + m, X, N + 1) > N) b = m; else a = m + 1;
      }
      need = a;
    }
    sneed[pat] = (unsigned char)need;
    for (int t = 0; t < NTHR; t++) {
      u64 B = (u64)tabp[THRN[t] - 1], Xt = X / (B * B);
      W0[pat * NTHR + t] = (unsigned short)(Xt == 0 ? 0 : count_min(P, spf, np, Xt, N + 1));
    }
  }
}

/* ---------- bit-parallel class sieve ----------
 * For a table prime p (p >= 31, so p does not divide Q) and d_k = d0 + k*Q:
 *   d_k mod p = a + k*b (mod p), a = d0 mod p, b = Q mod p,
 * and a + k*b = (k + c)*b with c = a * b^(-1) mod p.  Hence split(d_k) = S_p[(k + c) mod p] where
 * S_p[k] = [legtab(k*b mod p) == +1].  E_p stores S_p periodically extended to p + 128 bits, so
 * any 64-bit window starting at s < p is read from two words. */
#define WEXT 64 /* patterns carry WEXT extra words, so windows of up to WEXT words never wrap */
static u64 *Ebits[NTAB];
static int Binv[NTAB];
static u64 BM[NTAB], FM[NTAB]; /* Barrett floor((2^64-1)/p) and Lemire fastmod (2^64-1)/p + 1 */
static double PD[NTAB + 8], INVP[NTAB + 8], BINVD[NTAB + 8];
static void init_bitpatterns(void) {
  for (int t = 0; t < NTAB; t++) {
    int p = tabp[t];
    long long b = (long long)(Q % (u64)p), inv = 1;
    for (long long e = p - 2, base = b; e > 0; e >>= 1, base = base * base % p)
      if (e & 1) inv = inv * base % p;
    Binv[t] = (int)inv;
    int nbits = p + 64 * WEXT + 128, nw = nbits / 64 + 2;
    BM[t] = ~0ULL / (u64)p;
    FM[t] = ~0ULL / (u64)p + 1;
    Ebits[t] = calloc(nw, sizeof(u64));
    for (int k = 0; k < nbits; k++) {
      int res = (int)((long long)(k % p) * b % p);
      if (tabl[t][res] == 1) Ebits[t][k >> 6] |= 1ULL << (k & 63);
    }
  }
  for (int t = 0; t < NTAB + 8; t++) { /* padded to whole vectors of 8 */
    int tt = t < NTAB ? t : NTAB - 1;
    PD[t] = (double)tabp[tt];
    INVP[t] = 1.0 / (double)tabp[tt];
    BINVD[t] = (double)Binv[tt];
  }
}
static inline u64 window64(const u64 *E, int sbit) {
  int i = sbit >> 6, off = sbit & 63;
  return off ? (E[i] >> off) | (E[i + 1] << (64 - off)) : E[i];
}
/* mask over k in [0, K) of d_k certified by the sieving sets 0..need-1; result in A[0..W-1] */
static void class_sets_mask_old(u64 d0, long long K, int need, u64 *A, u64 *M) {
  int W = (int)((K + 63) / 64);
  for (int w = 0; w < W; w++) A[w] = ~0ULL;
  for (int j = 0; j < need; j++) {
    for (int w = 0; w < W; w++) M[w] = 0;
    for (int i = 0; i < SETSIZE; i++) {
      int t = j * SETSIZE + i, p = tabp[t];
      int c = (int)((d0 % (u64)p) * (u64)Binv[t] % (u64)p);
      int sb = c;
      const u64 *E = Ebits[t];
      for (int w = 0; w < W; w++) {
        M[w] |= window64(E, sb);
        sb += 64;
        while (sb >= p) sb -= p;
      }
    }
    for (int w = 0; w < W; w++) A[w] &= M[w];
  }
  if (K & 63) A[W - 1] &= (1ULL << (K & 63)) - 1;
}


/* offset c = (d0 mod p) * Binv mod p without division: Barrett for d0 mod p (r < p after at most
 * two corrections), Lemire's fastmod for x = r*Binv < p^2 < 2^32. */
static inline int offset_c(u64 d0, int t) {
  u64 p = (u64)tabp[t];
  u64 q = (u64)(((unsigned __int128)d0 * BM[t]) >> 64);
  u64 r = d0 - q * p;
  while (r >= p) r -= p;
  u64 x = r * (u64)Binv[t];
  return (int)(((unsigned __int128)(FM[t] * x) * p) >> 64);
}

/* division-free scalar version (any W <= WEXT); also the reference for the SIMD versions */
static void class_sets_mask_df(u64 d0, long long K, int need, u64 *A, u64 *M) {
  int W = (int)((K + 63) / 64);
  for (int w = 0; w < W; w++) A[w] = ~0ULL;
  for (int j = 0; j < need; j++) {
    for (int w = 0; w < W; w++) M[w] = 0;
    for (int i = 0; i < SETSIZE; i++) {
      int t = j * SETSIZE + i, c = offset_c(d0, t), off = c & 63;
      const u64 *E = Ebits[t] + (c >> 6);
      if (off == 0)
        for (int w = 0; w < W; w++) M[w] |= E[w];
      else
        for (int w = 0; w < W; w++) M[w] |= (E[w] >> off) | (E[w + 1] << (64 - off));
    }
    for (int w = 0; w < W; w++) A[w] &= M[w];
  }
  if (K & 63) A[W - 1] &= (1ULL << (K & 63)) - 1;
}

#if defined(__AVX512F__) && defined(__AVX512DQ__)
#define SIMD_NAME "AVX-512"
/* x mod p for 8 lanes in double precision; exact while x < 2^52 (quotient off by at most one) */
static inline __m512d modp_pd(__m512d x, __m512d p, __m512d ip) {
  __m512d q = _mm512_roundscale_pd(_mm512_mul_pd(x, ip), _MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC);
  __m512d r = _mm512_fnmadd_pd(q, p, x);
  r = _mm512_mask_add_pd(r, _mm512_cmp_pd_mask(r, _mm512_setzero_pd(), _CMP_LT_OQ), r, p);
  r = _mm512_mask_sub_pd(r, _mm512_cmp_pd_mask(r, p, _CMP_GE_OQ), r, p);
  return r;
}
/* W <= 16, d0 < 2^52: masks in two zmm registers.  Shifts by 64 give 0, so off = 0 needs no branch. */
static void class_sets_mask_simd(u64 d0, long long K, int need, u64 *A) {
  int W = (int)((K + 63) / 64);
  int cc[40];
  __mmask8 k0 = (__mmask8)(W >= 8 ? 0xFF : (1u << W) - 1);
  __mmask8 k1 = (__mmask8)(W <= 8 ? 0 : (W >= 16 ? 0xFF : (1u << (W - 8)) - 1));
  __m512d dv = _mm512_set1_pd((double)d0);
  __m512i a0 = _mm512_set1_epi64(-1), a1 = a0;
  for (int j = 0; j < need; j++) {
    int t0 = j * SETSIZE;
    for (int g = 0; g < SETSIZE; g += 8) {
      __m512d p = _mm512_loadu_pd(PD + t0 + g), ip = _mm512_loadu_pd(INVP + t0 + g);
      __m512d r = modp_pd(dv, p, ip);
      __m512d c = modp_pd(_mm512_mul_pd(r, _mm512_loadu_pd(BINVD + t0 + g)), p, ip); /* r*Binv < 2^28 */
      _mm256_storeu_si256((__m256i *)(cc + g), _mm512_cvttpd_epi32(c));
    }
    __m512i m0 = _mm512_setzero_si512(), m1 = m0;
    for (int i = 0; i < SETSIZE; i++) {
      const u64 *E = Ebits[t0 + i] + (cc[i] >> 6);
      __m128i so = _mm_cvtsi32_si128(cc[i] & 63), sl = _mm_cvtsi32_si128(64 - (cc[i] & 63));
      m0 = _mm512_or_si512(m0, _mm512_or_si512(_mm512_srl_epi64(_mm512_maskz_loadu_epi64(k0, E), so),
                                               _mm512_sll_epi64(_mm512_maskz_loadu_epi64(k0, E + 1), sl)));
      if (k1)
        m1 = _mm512_or_si512(m1, _mm512_or_si512(_mm512_srl_epi64(_mm512_maskz_loadu_epi64(k1, E + 8), so),
                                                 _mm512_sll_epi64(_mm512_maskz_loadu_epi64(k1, E + 9), sl)));
    }
    a0 = _mm512_and_si512(a0, m0);
    a1 = _mm512_and_si512(a1, m1);
  }
  _mm512_mask_storeu_epi64(A, k0, a0);
  if (k1) _mm512_mask_storeu_epi64(A + 8, k1, a1);
  if (K & 63) A[W - 1] &= (1ULL << (K & 63)) - 1;
}
#define SIMD_OK(d0, W) ((W) <= 16 && (d0) < (1ULL << 52))
#elif defined(__AVX2__)
#define SIMD_NAME "AVX2"
/* W <= 16: masks in four ymm registers; scalar division-free offsets */
static void class_sets_mask_simd(u64 d0, long long K, int need, u64 *A) {
  int W = (int)((K + 63) / 64);
  long long lm[20];
  for (int i = 0; i < 20; i++) lm[i] = (i < W) ? -1 : 0;
  __m256i k0 = _mm256_loadu_si256((const __m256i *)lm), k1 = _mm256_loadu_si256((const __m256i *)(lm + 4));
  __m256i k2 = _mm256_loadu_si256((const __m256i *)(lm + 8)), k3 = _mm256_loadu_si256((const __m256i *)(lm + 12));
  __m256i a0 = _mm256_set1_epi64x(-1), a1 = a0, a2 = a0, a3 = a0;
  for (int j = 0; j < need; j++) {
    __m256i m0 = _mm256_setzero_si256(), m1 = m0, m2 = m0, m3 = m0;
    for (int i = 0; i < SETSIZE; i++) {
      int t = j * SETSIZE + i, c = offset_c(d0, t);
      const long long *E = (const long long *)(Ebits[t] + (c >> 6));
      __m128i so = _mm_cvtsi32_si128(c & 63), sl = _mm_cvtsi32_si128(64 - (c & 63));
#define QS_STEP(m, k, o) m = _mm256_or_si256(m, _mm256_or_si256(_mm256_srl_epi64(_mm256_maskload_epi64(E + (o), k), so), \
                                            _mm256_sll_epi64(_mm256_maskload_epi64(E + (o) + 1, k), sl)))
      QS_STEP(m0, k0, 0);
      QS_STEP(m1, k1, 4);
      if (W > 8) { QS_STEP(m2, k2, 8); QS_STEP(m3, k3, 12); }
#undef QS_STEP
    }
    a0 = _mm256_and_si256(a0, m0); a1 = _mm256_and_si256(a1, m1);
    a2 = _mm256_and_si256(a2, m2); a3 = _mm256_and_si256(a3, m3);
  }
  _mm256_maskstore_epi64((long long *)A, k0, a0); _mm256_maskstore_epi64((long long *)A + 4, k1, a1);
  _mm256_maskstore_epi64((long long *)A + 8, k2, a2); _mm256_maskstore_epi64((long long *)A + 12, k3, a3);
  if (K & 63) A[W - 1] &= (1ULL << (K & 63)) - 1;
}
#define SIMD_OK(d0, W) ((W) <= 16)
#else
#define SIMD_NAME "none"
#define SIMD_OK(d0, W) 0
static void class_sets_mask_simd(u64 d0, long long K, int need, u64 *A) { (void)d0; (void)K; (void)need; (void)A; }
#endif

/* mask over k in [0, K) of d_k certified by the sieving sets 0..need-1; result in A[0..W-1] */
static void class_sets_mask(u64 d0, long long K, int need, u64 *A, u64 *M) {
  int W = (int)((K + 63) / 64);
  if (mask_impl == 1 || W > WEXT) { class_sets_mask_old(d0, K, need, A, M); return; }
  if (mask_impl == 0 && SIMD_OK(d0, W)) { class_sets_mask_simd(d0, K, need, A); return; }
  class_sets_mask_df(d0, K, need, A, M);
}

/* ---------- per-d processing ---------- */
static long long n_d, n_exact, n_resid, n_cls, n_cls2;
static FILE *resid_f;

static int pattern_of(u64 d) {
  int pat = 0, mul = 1;
  for (int i = 0; i < NSMALL; i++) {
    int s = compsym[i][d % CM[i]];
    if (s == 9) return -1;
    pat += (s + 1) * mul;
    mul *= 3;
  }
  return pat;
}

/* Phase 2b: closed-form lower bound.  If k primes q in (29, B_t] split and W0 is the weighted
 * count of pattern products m <= X/B_t^2, the products m, m*q_i, m*q_i*q_j (i<j) are distinct
 * minima <= X (Watkins' Lemma 3), so h(-d) >= W0 * (1 + 2k + 4*k(k-1)/2) = W0 * (2k^2 + 1). */
static long long n_bound;
/* d mod p for table prime t, division-free (Barrett; BM from init_bitpatterns) */
static inline u64 modp_t(u64 d, int t) {
  u64 p = (u64)tabp[t], r = d - (u64)(((unsigned __int128)d * BM[t]) >> 64) * p;
  while (r >= p) r -= p;
  return r;
}
static u64 *bpA, *bpM;
static int bound_certify(u64 d, int pat) {
  long long k = 0;
  int t = 0;
  for (int i = 0; i < NTAB; i++) {
    if (tabl[i][modp_t(d, i)] == 1) k++;
    if (i + 1 == THRN[t]) {
      long long w = W0[pat * NTHR + t];
      if (w > 0 && w * (2 * k * k + 1) > N) return 1;
      if (++t == NTHR) break;
    }
  }
  return 0;
}

/* symbol (-d|p): table lookup for the sieving-set primes, Jacobi otherwise */
static inline int sym(u64 d, int k) { /* k = index into primes[] */
  int p = primes[k];
  if (p >= 31 && p <= tabp[NTAB - 1]) return tabl[k - 10][modp_t(d, k - 10)]; /* primes[10] == 31 */
  return kron_minus_d(d, p);
}

static int exact_certify(u64 d) {
  u64 X = isqrt64(d / 4);
  static u64 P[200000];
  static char spf[200000];
  int np = 0, ns = 0, next = 8;
  for (int k = 0; k < nprimes && (u64)primes[k] <= X; k++) {
    int s = sym(d, k);
    if (s == -1) continue;
    P[np] = primes[k];
    spf[np++] = (char)(s == 1);
    if (s == 1 && ++ns >= next) {
      if (count_min(P, spf, np, X, N + 1) > N) return 1;
      next = next + next / 2;
    }
  }
  return count_min(P, spf, np, X, N + 1) > N;
}

static void fallback_d(u64 d, int pat);
static inline void handle_d(u64 d, int need, int pat) {
  n_d++;
  if (need > SMAX) goto bound;
  for (int j = 0; j < need; j++) {
    int ok = 0;
    for (int i = 0; i < SETSIZE; i++)
      if (tabl[j * SETSIZE + i][modp_t(d, j * SETSIZE + i)] == 1) { ok = 1; break; } /* = legtab[j][i] */
    if (!ok) goto bound;
  }
  return;
bound:
  if (bound_certify(d, pat)) {
    n_bound++;
    if (check_bound && !exact_certify(d)) { n_bound_bad++; fprintf(resid_f, "BOUNDBAD %llu\n", d); }
    return;
  }
  n_exact++;
  if (exact_certify(d)) return;
  n_resid++;
  fprintf(resid_f, "%llu\n", d);
}

/* phases 2b and 3 for a d whose sets did not certify it (bit-parallel path) */
static void fallback_d(u64 d, int pat) {
  if (bound_certify(d, pat)) {
    n_bound++;
    if (check_bound && !exact_certify(d)) { n_bound_bad++; fprintf(resid_f, "BOUNDBAD %llu\n", d); }
    return;
  }
  n_exact++;
  if (exact_certify(d)) return;
  n_resid++;
  fprintf(resid_f, "%llu\n", d);
}

/* ---------- work units and logging ---------- */
typedef struct { u64 lo, hi, seglo; int mode; int chunk; } unit; /* mode 0 direct, 1 class */
static unit *units;
static int nunits;

static void add_unit(u64 lo, u64 hi, u64 seglo, int mode, int chunk) {
  units = realloc(units, sizeof(unit) * (nunits + 1));
  units[nunits++] = (unit){lo, hi, seglo, mode, chunk};
}

static void make_units(u64 lo, u64 hi, int nproc) {
  for (int k = 0; k < 64; k++) {
    u64 a = (k == 0) ? 0 : (1ULL << k), b = (k == 63) ? ~0ULL : (1ULL << (k + 1)) - 1;
    if (b < lo || a > hi) continue;
    if (a < lo) a = lo;
    if (b > hi) b = hi;
    if (b - a + 1 < Q) {
      u64 parts = (u64)nproc * 8, len = b - a + 1, step = (len + parts - 1) / parts;
      if (step < 1) step = 1;
      for (u64 s = a; s <= b; s += step) add_unit(s, (s + step - 1 < b) ? s + step - 1 : b, a, 0, 0);
    } else {
      for (int c = 0; c < 23 * 29; c++) add_unit(a, b, a, 1, c);
    }
  }
}

static void wlog(FILE *lf, int w, int done, int total, double t0, const char *tag) {
  double el = now() - t0, eta = done > 0 ? el * (total - done) / done : -1;
  time_t tt = time(NULL);
  char ts[64];
  strftime(ts, sizeof ts, "%Y-%m-%d %H:%M:%S", localtime(&tt));
  fprintf(lf, "%s worker %d %s: units %d/%d (%.2f%%), d processed %lld, bound %lld, exact %lld, residual %lld, "
              "classes %lld (with >= 2 d: %lld), bound-check failures %lld, elapsed %.0f s, ETA %.0f s\n",
          ts, w, tag, done, total, total ? 100.0 * done / total : 100.0, n_d, n_bound, n_exact, n_resid, n_cls, n_cls2, n_bound_bad, el, eta);
  fflush(lf);
}

static void run_worker(int w, int nproc, double interval, const char *outdir) {
  char fn[4096];
  snprintf(fn, sizeof fn, "%s/residual.%d.txt", outdir, w);
  resid_f = fopen(fn, "w");
  snprintf(fn, sizeof fn, "%s/log.%d.txt", outdir, w);
  FILE *lf = fopen(fn, "w");
  if (!resid_f || !lf) { perror("open"); exit(2); }
  int total = 0, done = 0;
  for (int u = w; u < nunits; u += nproc) total++;
  double t0 = now(), tnext = t0 + interval;
  wlog(lf, w, 0, total, t0, "start");
  unsigned char *sneed = malloc(NPAT);
  W0 = malloc(sizeof(unsigned short) * NPAT * NTHR);
  long long Kmax = 1;
  for (int u = w; u < nunits; u += nproc) {
    long long Ku = (long long)((units[u].hi - units[u].lo) / Q) + 2;
    if (Ku > Kmax) Kmax = Ku;
  }
  bpA = malloc(sizeof(u64) * (Kmax / 64 + 2));
  bpM = malloc(sizeof(u64) * (Kmax / 64 + 2));
  u64 cur_seg = ~0ULL;
  for (int u = w; u < nunits; u += nproc) {
    unit U = units[u];
    if (max_chunk >= 0 && U.mode == 1 && U.chunk >= max_chunk) { done++; continue; }
    if (U.mode == 0) {
      if (U.seglo != cur_seg) { build_pattern_table(sneed, isqrt64(U.seglo / 4)); cur_seg = U.seglo; }
      for (u64 d = U.lo; d <= U.hi; d++) {
        if (d <= 4) { /* d = 3, 4: outside Watkins' d > 4; hand to postproc */
          if (d >= 3) { n_resid++; fprintf(resid_f, "%llu\n", d); }
          continue;
        }
        if ((d & 0xFFFFF) == 0 && now() > tnext) { wlog(lf, w, done, total, t0, "progress"); tnext += interval; }
        int pat = pattern_of(d);
        if (pat < 0) continue;
        int need = sneed[pat];
        if (force_all && need == 0) need = 1;
        if (need == 0) { n_d++; continue; }
        handle_d(d, need, pat);
      }
    } else {
      /* class mode: fix residues mod 23 and 29 by chunk, loop over the other components */
      if (U.seglo != cur_seg) { build_pattern_table(sneed, isqrt64(U.seglo / 4)); cur_seg = U.seglo; }
      int r23 = U.chunk % 23, r29 = U.chunk / 23;
      int s23 = compsym[8][r23], s29 = compsym[9][r29];
      int basepat = (s23 + 1) * 6561 + (s29 + 1) * 19683; /* 3^8, 3^9 */
      u64 rbase = (u64)(((i128)r23 * cmE[8] + (i128)r29 * cmE[9]) % Q);
      int idx[8] = {0};
      const int dims[8] = {16, 9, 5, 7, 11, 13, 17, 19};
      const int mul[8] = {1, 3, 9, 27, 81, 243, 729, 2187};
      long long iter = 0;
      for (;;) {
        int pat = basepat, bad = 0;
        u64 r = rbase;
        for (int i = 0; i < 8; i++) {
          int s = compsym[i][idx[i]];
          if (s == 9) { bad = 1; break; }
          pat += (s + 1) * mul[i];
        }
        if (!bad) {
          int need = sneed[pat];
          if (force_all && need == 0) need = 1;
          if (need > 0) {
            for (int i = 0; i < 8; i++) r = (u64)(((i128)r + (i128)idx[i] * cmE[i]) % Q);
            u64 k0 = (U.lo > r) ? (U.lo - r + Q - 1) / Q : 0;
            u64 d0 = r + k0 * Q;
            long long K = (d0 <= U.hi) ? (long long)((U.hi - d0) / Q) + 1 : 0;
            if (!scalar_only && K >= kmin_bp && need <= SMAX) {
              class_sets_mask(d0, K, need, bpA, bpM);
              n_d += K;
              int W = (int)((K + 63) / 64);
              for (int w = 0; w < W; w++) {
                u64 z = ~bpA[w];
                if (w == W - 1 && (K & 63)) z &= (1ULL << (K & 63)) - 1;
                while (z) {
                  int b = __builtin_ctzll(z);
                  z &= z - 1;
                  fallback_d(d0 + (u64)(64 * w + b) * Q, pat);
                }
              }
            } else {
              for (u64 d = d0; d <= U.hi; d += Q) handle_d(d, need, pat);
            }
            n_cls++;
            if (K >= 2) n_cls2++;
          }
        }
        if ((++iter & 0xFFFFF) == 0 && now() > tnext) { wlog(lf, w, done, total, t0, "progress"); tnext += interval; }
        int i = 0;
        while (i < 8) { if (++idx[i] < dims[i]) break; idx[i] = 0; i++; }
        if (i == 8) break;
      }
    }
    done++;
    if (now() > tnext) { wlog(lf, w, done, total, t0, "progress"); tnext += interval; }
  }
  wlog(lf, w, done, total, t0, "finished");
  fclose(lf);
  fclose(resid_f);
  exit(0);
}

/* -V self-test: symbol tables versus direct Kronecker symbols on pseudo-random d */
static int selftest(void) {
  u64 x = 88172645463325252ULL;
  long long bad = 0, tested = 0;
  for (int t = 0; t < 2000000; t++) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    u64 d = (x % ((1ULL << 62) - 5)) + 5;
    int pat = pattern_of(d);
    if (pat < 0) continue;
    tested++;
    int q = pat;
    for (int i = 0; i < NSMALL; i++) {
      int s = q % 3 - 1;
      q /= 3;
      if (s != kron_minus_d(d, SP[i])) bad++;
    }
    for (int j = 0; j < SMAX; j++)
      for (int i = 0; i < SETSIZE; i++)
        if (legtab[j][i][d % (u64)setp[j][i]] != kron_minus_d(d, setp[j][i])) bad++;
    for (int k = 0; k < NTAB + 20; k++)
      if (sym(d, k) != kron_minus_d(d, primes[k])) bad++;
  }
  /* bit-parallel class mask versus direct per-d set checks */
  {
    static u64 A[64], Mb[64];
    long long bpbad = 0, bptested = 0;
    u64 xs = x;
    for (int impl = 0; impl < 3; impl++) {
    mask_impl = impl;
    x = xs;
    for (int t = 0; t < 3000; t++) {
      x ^= x << 13; x ^= x >> 7; x ^= x << 17;
      u64 d0 = (x % (1ULL << 50)) + 5;
      long long K = 64 + (long long)(x % 1900);
      int need = 1 + (int)((x >> 20) % 8);
      class_sets_mask(d0, K, need, A, Mb);
      for (long long k = 0; k < K; k++) {
        u64 d = d0 + (u64)k * Q;
        int ok = 1;
        for (int j = 0; j < need && ok; j++) {
          int any = 0;
          for (int i = 0; i < SETSIZE; i++) if (kron_minus_d(d, setp[j][i]) == 1) { any = 1; break; }
          if (!any) ok = 0;
        }
        int bit = (int)((A[k >> 6] >> (k & 63)) & 1);
        bptested++;
        if (bit != ok) bpbad++;
      }
    }
    }
    mask_impl = 0;
    printf("self-test (bit-parallel, implementations SIMD=%s / original / division-free): %lld (d, sets) cases, %lld mismatches\n", SIMD_NAME, bptested, bpbad);
    bad += bpbad;
  }
  printf("self-test: %lld valid d tested, %lld symbol mismatches -> %s\n", tested, bad, bad ? "FAIL" : "PASS");
  return bad ? 4 : 0;
}

static void usage(const char *p) {
  fprintf(stderr, "usage: %s -N classbound -a lo -b hi [-j nproc (12)] [-i interval_seconds (1200)] [-o outdir (.)] [-T]\n"
                  "  -T  test mode: every class is examined individually (checks class enumeration)\n"
                  "  -V  self-test of the symbol tables against direct Kronecker symbols, then exit\n"
                  "  -C  verify every phase-2b bound certification by the exact count (slow; for testing)\n"
                  "  -S  scalar only: disable the bit-parallel class sieve (for cross-checking)\n"
                  "  -K  minimum class length for bit-parallel sieving (default 10; small values for testing)\n"
                  "  -M  class-mask implementation: 0 SIMD (default), 1 original, 2 division-free scalar\n"
                  "  -U  benchmarking: process only class-mode chunks < U (incomplete coverage)\n", p);
  exit(1);
}

int main(int argc, char **argv) {
  u64 lo = 0, hi = 0;
  int nproc = 12;
  double interval = 1200;
  const char *outdir = ".";
  int opt;
  N = 0;
  int do_selftest = 0;
  while ((opt = getopt(argc, argv, "N:a:b:j:i:o:TVCSK:M:U:")) != -1) {
    switch (opt) {
      case 'N': N = atoi(optarg); break;
      case 'a': lo = strtoull(optarg, NULL, 10); break;
      case 'b': hi = strtoull(optarg, NULL, 10); break;
      case 'j': nproc = atoi(optarg); break;
      case 'i': interval = atof(optarg); break;
      case 'o': outdir = optarg; break;
      case 'T': force_all = 1; break;
      case 'V': do_selftest = 1; break;
      case 'C': check_bound = 1; break;
      case 'S': scalar_only = 1; break;
      case 'K': kmin_bp = atoll(optarg); break;
      case 'M': mask_impl = atoi(optarg); break;
      case 'U': max_chunk = atoi(optarg); break;
      default: usage(argv[0]);
    }
  }
  if (do_selftest) { init_primes(); init_bitpatterns(); return selftest(); }
  if (N <= 0 || hi < lo || hi == 0 || nproc < 1 || interval <= 0 || hi >= (1ULL << 63)) usage(argv[0]);
  if (lo < 3) lo = 3;
  mkdir(outdir, 0755);
  init_primes();
  init_bitpatterns();
  make_units(lo, hi, nproc);
  printf("qsieve: N = %d, d in [%llu, %llu], %d processes, log interval %.0f s, %d work units, outdir %s, mask %s%s\n",
         N, lo, hi, nproc, interval, nunits, outdir, mask_impl == 0 ? SIMD_NAME : mask_impl == 1 ? "original" : "division-free",
         max_chunk >= 0 ? " [-U: INCOMPLETE COVERAGE]" : "");
  fflush(stdout);
  double t0 = now();
  for (int w = 0; w < nproc; w++) {
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return 2; }
    if (pid == 0) run_worker(w, nproc, interval, outdir);
  }
  int status, failed = 0;
  while (wait(&status) > 0)
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) failed++;
  printf("qsieve: all workers finished in %.1f s, failed workers: %d\n", now() - t0, failed);
  return failed ? 3 : 0;
}
