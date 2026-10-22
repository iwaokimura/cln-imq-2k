# Compare the list of Garcia-Grenie-Lee-Molteni (arXiv:2610.14257; one line per class number n = 1..2000,
# the vector of discriminants D with h(D) = n) with our list of the fields with h <= 2000 ("d h" per line,
# increasing d). Usage: python3 -I compare_gglm2000.py classes-list-2000.txt imq_h2000.txt.xz
import sys, lzma, hashlib
gglm, ours = sys.argv[1], sys.argv[2]
pairs = []
raw = open(gglm, 'rb').read()
print("sha256 of", gglm.rsplit('/', 1)[-1], hashlib.sha256(raw).hexdigest())
lines = [l for l in raw.decode().split('\n') if l.strip()]
assert len(lines) == 2000, len(lines)
for n, l in enumerate(lines, 1):
    l = l.strip(); assert l[0] == '[' and l[-1] == ']'
    body = l[1:-1].strip()
    for t in (body.split(',') if body else []):
        D = int(t); assert D < 0
        pairs.append((-D, n))
pairs.sort()
assert len(set(p[0] for p in pairs)) == len(pairs), "duplicate discriminant"
g = ''.join(f"{d} {h}\n" for d, h in pairs).encode()
o = lzma.open(ours).read()
print("gglm pairs", len(pairs), "max d", max(p[0] for p in pairs))
print("ours lines", o.count(b'\n'))
print("sha256 gglm", hashlib.sha256(g).hexdigest())
print("sha256 ours", hashlib.sha256(o).hexdigest())
print("IDENTICAL" if g == o else "DIFFERENT")
if g != o:
    os_ = set(tuple(map(int, l.split())) for l in o.decode().splitlines())
    gs = set(pairs)
    print("only gglm", sorted(gs - os_)[:20], "only ours", sorted(os_ - gs)[:20])
