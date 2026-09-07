#!/usr/bin/env python3
# signature_census.py — classify the diff between two signature snapshots
# (scripts/signature_snapshot.lean output) for a re-pin/landing record.
#   usage: scripts/signature_census.py PRE.txt POST.txt OUT.txt
# Prints the totals (ADDED / REMOVED / CHANGED by class) and writes the
# per-name lists to OUT. Classes of a CHANGED statement: `binder-only` — the
# conclusion and every non-fuel premise are unchanged (fuel binders/hypotheses
# inserted or dropped, instance names, bracket kinds, binder order);
# `premise-text` — a non-fuel premise's text changed; `shape` — the
# conclusion changed; each non-binder-only change carries a CAUSE bucket
# (fuel-token-only / Z1-kill / Z2-alloc / Z2-mem-repr / engine-wrapper /
# LemLib-map / R2-fragment / printing-* / UNEXPLAINED). A heuristic
# instrument, not a gate ([AGENT 2026-09-07, L2]; record
# docs/2026-09-07_l2-repin-notes.md).
import re,sys,collections
HDR=re.compile(r'^([a-zA-Z]+) (\S+) :(.*)$')
def parse(path):
    d=collections.OrderedDict(); cur=None
    for line in open(path):
        line=line.rstrip('\n'); m=HDR.match(line)
        if m and not line.startswith(' '):
            cur=m.group(2); d[cur]=[m.group(1), m.group(3).strip()]
        elif cur is not None: d[cur][1]+=' '+line.strip()
    return {k:(v[0],' '.join(v[1].split())) for k,v in d.items()}
OPEN='([{⟨⌜'; CLOSE=')]}⟩⌝'
def split_forall(s):
    """'∀ b1 b2, rest' → ([b1,b2], rest); else ([], s)"""
    if not s.startswith('∀ '): return [], s
    depth=0; i=2; cur=''; bs=[]
    while i < len(s):
        c=s[i]
        if c in OPEN: depth+=1
        elif c in CLOSE: depth-=1
        if depth==0 and c==',': 
            if cur.strip(): bs.append(cur.strip())
            return bs, s[i+1:].strip()
        if depth==0 and c==' ':
            if cur.strip(): bs.append(cur.strip()); cur=''
        else: cur+=c
        i+=1
    return bs, ''
def split_arrows(s):
    """top-level split at ' → ' (not inside brackets); returns list of segments"""
    segs=[]; depth=0; i=0; cur=''
    while i < len(s):
        c=s[i]
        if c in OPEN: depth+=1
        elif c in CLOSE: depth-=1
        if depth==0 and s.startswith(' → ', i):
            segs.append(cur.strip()); cur=''; i+=3; continue
        cur+=c; i+=1
    segs.append(cur.strip()); return segs
def flatten(s):
    prem=[]
    segs=split_arrows(s)
    for seg in segs[:-1]:
        while seg.startswith('∀ '):
            bs, body = split_forall(seg); prem += bs; seg = body
            if body=='' : break
        if seg: prem.append(seg)
    concl=segs[-1]
    # a conclusion of the form ∀ xs, body: the binders are premises, body the conclusion
    while concl.startswith('∀ '):
        bs, body = split_forall(concl); prem += bs
        inner = split_arrows(body)
        for seg in inner[:-1]:
            while seg.startswith('∀ '):
                bs2, b2 = split_forall(seg); prem += bs2; seg = b2
            if seg: prem.append(seg)
        concl = inner[-1]
    return prem, concl
def nb(p): return re.sub(r'^[\{\[\(]|[\}\]\)]$','',p)   # binder bracket kind is a binder-only change
def expand(ps):
    out=[]
    for p in ps:
        q=nb(p); m=re.match(r'^([^:()\[\]{}]+) : (.*)$', q)
        if m and ' ' in m.group(1).strip() and not m.group(1).strip().startswith('∀'):
            for nm in m.group(1).split(): out.append(f"{nm} : {m.group(2)}")
        else: out.append(q)
    return out
FUEL=re.compile(r'LemFuel|lemDefaultFuel|driverFuel|evalDepth|peDepth|\bpot\b|esize|ProcsDepth|FragProcsFuel|FragFuel')
isfuel=lambda p: bool(FUEL.search(p))
def normalize(t):
    t=re.sub(r'\binst_\d+\b','inst',t); t=re.sub(r'inst✝\S*','inst',t)
    return t
pre={k:(v[0],normalize(v[1])) for k,v in parse(sys.argv[1]).items()}
post={k:(v[0],normalize(v[1])) for k,v in parse(sys.argv[2]).items()}
added=[k for k in post if k not in pre]; removed=[k for k in pre if k not in post]
changed=[k for k in post if k in pre and pre[k]!=post[k]]
cls=collections.OrderedDict((c,[]) for c in ['binder-only','premise-text','shape','kind'])
detail={}
for k in changed:
    (kp,tp),(kq,tq)=pre[k],post[k]
    if kp!=kq: cls['kind'].append(k); continue
    pp,cp=flatten(tp); pq,cq=flatten(tq)
    if cp!=cq: cls['shape'].append(k); detail[k]=('concl',cp,cq); continue
    np_=sorted(expand([p for p in pp if not isfuel(p)])); nq=sorted(expand([p for p in pq if not isfuel(p)]))
    if np_==nq: cls['binder-only'].append(k)
    else:
        cls['premise-text'].append(k)
        dp=[p for p in np_ if p not in nq]; dq=[p for p in nq if p not in np_]
        detail[k]=('prem',' | '.join(dp),' | '.join(dq))
print(f"pre entries {len(pre)}  post entries {len(post)}")
print(f"ADDED {len(added)}  REMOVED {len(removed)}  CHANGED {len(changed)}")
for c,l in cls.items(): print(f"  {c}: {len(l)}")
norm=lambda s: re.sub(r'lemDefaultFuel|CerbFuel\.driverFuel','LemFuel.fuel',s)
def cause(k, d):
    kind,a,b=d
    txt=a+' '+b
    if norm(a)==norm(b): return 'fuel-token-only'
    if '⋯' in txt: return 'printing-elision'
    if re.sub(r'generic_expr core_run_annotation Unit sym','expr core_run_annotation',a)==re.sub(r'generic_expr core_run_annotation Unit sym','expr core_run_annotation',b): return 'printing-abbrev'
    if re.search(r'symAdd|fmapAddBy|LemOrdering|lemCmpToOrd|treeMap|symOrd l',txt): return 'LemLib-map'
    if re.search(r'intToBytes|bytesToInt|2 \^ 64|2147483647|9223372036854775807|Img|storable|bs ≠',txt): return 'Z2-mem-repr'
    if FUEL.search(txt) or re.search(r'≤ \d+$|= \d+$|≤ bound',txt): return 'R2-fragment'
    if re.search(r'UB009|MerrOther|function pointer|provenance|Prov_symbolic|killM|kill',txt) and 'kill' in k.lower() or 'killM' in txt: return 'Z1-kill'
    if re.search(r'PrefMalloc|lastUsed|requested|UnallocatedBytes|get_with_address|0 < alignN|0 ≤ sizeN|writeBytesTo|allocateObject|allocateRegion|sizeN|allocations|0 < al\b|0 < al[₁₂]|0 ≤ n\b|0 ≤ sz|0 < sz|regionCost|allocCost',txt): return 'Z2-alloc'
    if re.search(r'_lemFuel|get_ctx|subst_sym|lemSize|Core_aux',txt): return 'engine-wrapper'
    if re.search(r'FragFuel|Frag\b|Frag\.',txt): return 'R2-fragment'
    return 'UNEXPLAINED'
out=open(sys.argv[3],'w')
out.write("== REMOVED (%d)\n"%len(removed)+'\n'.join(removed)+"\n== ADDED (%d)\n"%len(added)+'\n'.join(added)+"\n")
buckets=collections.Counter()
for c in ['kind','shape','premise-text']:
    out.write(f"== CHANGED/{c} ({len(cls[c])})\n")
    for k in cls[c]:
        d=detail.get(k); cz=cause(k,d) if d else '?'
        buckets[(c,cz)]+=1
        out.write(f"{k}\t{cz}\n")
        if d and cz!='fuel-token-only':
            out.write(f"    PRE : {d[1][:300]}\n    POST: {d[2][:300]}\n")
out.write(f"== CHANGED/binder-only ({len(cls['binder-only'])})\n"+'\n'.join(cls['binder-only'])+"\n")
out.close()
print("cause buckets:"); 
for (c,cz),n in sorted(buckets.items()): print(f"  {c:13s} {cz:16s} {n}")
