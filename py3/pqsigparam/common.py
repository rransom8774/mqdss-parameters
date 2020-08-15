
# Authors: Robert Ransom

# This software is released to the public domain.

# To the extent permitted by law, this software is provided WITHOUT ANY
# WARRANTY WHATSOEVER.

import sys
import math
import operator
import fractions
import functools
import itertools
import collections

def log2(x):
    if isinstance(x, fractions.Fraction):
        return math.log2(x.numerator) - math.log2(x.denominator)
    return math.log2(x)

class FieldParams(object):
    __slots__ = ('q', 'sampling_bits', 'log2diverg1')
    def __init__(self, q, sampling_bits=None):
        self.q = q
        self.sampling_bits = sampling_bits or q.bit_length()
        self.log2diverg1 = None
        pass
    def __repr__(self):
        return 'F{q=%r, b=%r}' % (self.q, self.sampling_bits)
    def sampling_max_preimages(self):
        q = self.q
        b = self.sampling_bits
        P = (2**b) // q   # NOTE floor division
        if (2**b) % q != 0:
            P += 1
            pass
        return P
    def sampling_min_preimages(self):
        q = self.q
        b = self.sampling_bits
        P = (2**b) // q   # NOTE floor division
        return P
    def log2diverg_vector(self, n):
        # DJB divergence-20180430, Theorem 2.1
        # divergence <= (Pq/(2**b))**n
        # P = # of preimages; P <= ceil((2**b)/q) by Theorems 2.2 and 2.3
        if self.log2diverg1 == None:
            q = self.q
            b = self.sampling_bits
            P = self.sampling_max_preimages()
            self.log2diverg1 = math.log1p((P*q - 2**b)/(2**b))/math.log(2)
            pass
        return self.log2diverg1 * n
    pass

# divergence bounds

def log2diverg_sorting(n, randbits):
    # DJB divergence-20180430, Theorems 3.1, 4.1, 5.1
    # divergence <= product of [1 + i/2**b for i in range(1, n)]
    b = randbits
    lndiverg = math.fsum(math.log1p(i/(2**b)) for i in range(1, n))
    return lndiverg/math.log(2)

# combinatorial functions

def binom(n, w):
    return (functools.reduce(operator.mul,
                             (n - i for i in range(w)), 1) //
            math.factorial(w))

def trinomial(w0, w1, w2):
    n = w0 + w1 + w2
    return binom(n, w1+w2) * binom(w1+w2, w2)

def tetranomial(w0, w1, w2, w3):
    n = w0 + w1 + w2 + w3
    return binom(n, w1+w2+w3) * binom(w1+w2+w3, w2+w3) * binom(w2+w3, w3)

# utility functions for 5-pass q2 protocols

def pfwdist(n, w, p):
    """Computes the distribution produced by puncturing the uniform
    distribution of fixed-weight vectors."""
    assert p <= n
    assert w <= n
    dist = list(itertools.repeat(None, min(w, p) + 1))
    N = 0
    for wp in range(min(w, p) + 1):
        punctcount = binom(p, wp)
        vectcount = binom(n - p, w - wp)
        dist[wp] = (vectcount, punctcount)
        N = N + (vectcount * punctcount)
        pass
    assert N == binom(n, w)
    return (N, dist)

def pfw_log2probs(n, w, p):
    N, dist = pfwdist(n, w, p)
    return [log2(fractions.Fraction(pc, N)) for (vc, pc) in dist]

def pfw_log2guessprob(n, w, p):
    return max(pfw_log2probs(n, w, p))

def l2costs_add(lwx, lwy):
    if abs(lwx - lwy) >= 64:
        # too far apart to represent the increase in cost
        return max(lwx, lwy)
    l2scale = min(lwx, lwy)
    slwx = lwx - l2scale
    slwy = lwy - l2scale
    swtotal = 2**(slwx) + 2**(slwy)
    slwtotal = math.log2(swtotal)
    lwtotal = slwtotal + l2scale
    return lwtotal

def q2_chal1_guessprobs_exact(field, r):
    """rv[w] = maximal probability of guessing exactly w elements of ch_1
    
    sampling bias is accounted for"""
    Pmax = field.sampling_max_preimages()
    Pmin = field.sampling_min_preimages()
    b = field.sampling_bits
    # assume the attacker will guess maximal-probability challenges
    pelemmax = fractions.Fraction(Pmax, 2**b)
    pelemmin = fractions.Fraction(Pmin, 2**b)
    # prob. of guessing w specific elements is (pelem**w)*((1-pelem)**(r-w));
    #   can be done for any of binom(r,w) sets of elements
    return [(pelemmax**w)*((1-pelemmin)**(r-w))*binom(r, w) for w in range(r+1)]

def q2_chal1_guessprobs_cumulative(field, r):
    """rv[w] = maximal probability of guessing at least w elements of ch_1
    
    sampling bias is accounted for"""
    rv = list(itertools.repeat(None, r+1))
    exactprobs = q2_chal1_guessprobs_exact(field, r)
    w = r
    acc = 0
    while w >= 0:
        acc = acc + exactprobs[w]
        rv[w] = acc
        w = w - 1
        pass
    return rv

@functools.lru_cache(maxsize=16)
def q2_chal1_guessprobs_log2cum(field, r):
    "rv[w] = upper bound on log_2(prob of guessing at least w elems of ch_1)"
    return list(map(log2, q2_chal1_guessprobs_cumulative(field, r)))

def q2_chal2_guessprob_fw(r0, r1, randbits, kzguess):
    r = r0 + r1
    l2div = 0
    if randbits != None:
        l2div = log2diverg_sorting(r, randbits)
        pass
    return pfw_log2guessprob(r, r1, kzguess) + l2div

def q2_chal2_guessprobs_fw(r0, r1, randbits=31):
    r = r0 + r1
    return [q2_chal2_guessprob_fw(r0, r1, randbits, kzg)
            for kzg in range(r+1)]

def q2_seclevel_fw(field, r0, r1, randbits=31):
    r = r0 + r1
    ch1_lgps = q2_chal1_guessprobs_log2cum(field, r)
    ch2_lgps = q2_chal2_guessprobs_fw(r0, r1, randbits)
    return min(map(l2costs_add,
                   map(operator.neg, ch1_lgps),
                   map(operator.neg, ch2_lgps)))

# generic signature component size sets

SigParams = collections.namedtuple('SigParams', ('preimagebytes', 'hashbytes'))

spc1 = SigParams(16, 32)
spc2 = SigParams(24, 32)
spc3 = SigParams(24, 48)
spc4 = SigParams(32, 48)
spc5 = SigParams(32, 64)

spb112 = SigParams(14, 28)
spb96  = SigParams(12, 24)
spb80  = SigParams(10, 20)

spc1a = SigParams(20, 32)

spb112git = SigParams(14, 20)

# parameter set optimization for size, 5-pass, utility functions

@functools.lru_cache(maxsize=None)
def q2_minimize_r0_fixedr(field, sp, r):
    """Return largest r0 achieving the security level specified by sp, or
    None if r is too small."""
    minsec = sp.preimagebytes * 8
    # maximum security level is achieved at r1=r//2, r0=r-r1
    # convention from MQDSS: signature size decreases as r1 decreases
    # when r1 <= r/2, security level decreases as r1 decreases
    # find minimum r1 such that security level >= minsec
    r1max = r//2
    r1min = 1
    r1 = r1max
    while r1min < r1max:
        r0 = r - r1
        seclevel = q2_seclevel_fw(field, r0, r1)
        if seclevel < minsec:
            r1min = r1 + 1
            pass
        else:
            r1max = r1
            pass
        r1 = (r1min + r1max) // 2
        pass
    if r1min > r1max:
        return
    r1 = r1min
    r0 = r - r1
    seclevel = q2_seclevel_fw(field, r0, r1)
    if seclevel >= minsec:
        return r0

def q2_minimize_sigsize(kp, sp, fp, evaluate_sigsize):
    field = kp.field
    minsec = sp.preimagebytes * 8
    results = list()
    minsize = None
    r = minsec   # cannot possibly use less than b rounds for b-bit security
    while (minsize == None or
           minsize >= evaluate_sigsize(kp, sp, fp, r-1, 1)):
        r0 = q2_minimize_r0_fixedr(field, sp, r)
        if r0 != None:
            r1 = r - r0
            size = evaluate_sigsize(kp, sp, fp, r0, r1)
            if minsize == None or minsize > size:
                minsize = size
                pass
            results.append((size, r0, r1))
            pass
        r = r + 1
        pass
    results.sort()
    return results[0:10]

