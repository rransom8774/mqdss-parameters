
import sys
import math
import operator
import fractions
import functools
import itertools
import collections

class FieldParams(object):
    __slots__ = ('q', 'sampling_bits', 'log2diverg1')
    def __init__(self, q, sampling_bits=None):
        self.q = q
        self.sampling_bits = sampling_bits or q.bit_length()
        self.log2diverg1 = None
        pass
    def __repr__(self):
        return 'F{q=%r, b=%r}' % (q, sampling_bits)
    def sampling_max_preimages(self):
        q = self.q
        b = self.sampling_bits
        P = (2**b) // q   # NOTE floor division
        if (2**b) % q != 0:
            P += 1
            pass
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

class ParamSet(object):
    __slots__ = ('field', 'r')
    def __init__(self, field, r):
        self.field = field
        self.r = r
        pass
    
    
    pass

# FIXME signature component size sets here               

# FIXME divergence bounds               

def log2diverg_sorting(n, randbits):
    # DJB divergence-20180430, Theorems 3.1, 4.1, 5.1
    # divergence <= product of [1 + i/2**b for i in range(1, n)]
    b = randbits
    lndiverg = math.fsum(math.log1p(i/(2**b)) for i in range(1, n))
    return lndiverg/math.log(2)

# FIXME combinatorial functions               

def binom(n, w):
    return (functools.reduce(operator.mul,
                             (n - i for i in range(w)), 1) //
            math.factorial(w))

def pfwdist(n, w, p):
    """Computes distribution produced by puncturing the uniform
    distribution of fixed-weight vectors.
    
    FIXME"""   
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
    return [math.log2(pc / N) for (vc, pc) in dist]

def pfw_log2guessprob(n, w, p):
    return max(pfw_log2probs(n, w, p))

# FIXME evaluation, 5-pass, step 1               

def mqdss5p_chal1_guessprobs_exact(field, r):
    """
    rv[w] = maximal probability of guessing exactly w elements of ch_1
    
    sampling bias is accounted for
    """
    P = field.sampling_max_preimages()
    b = field.sampling_bits
    # assume the attacker will guess maximal-probability challenges
    pelem = fractions.Fraction(P, 2**b)
    # prob. of guessing w specific elements is (pelem**w)*((1-pelem)**(r-w));
    #   can be done for any of binom(r,w) sets of elements
    return [(pelem**w)*((1-pelem)**(r-w))*binom(r, w) for w in range(r+1)]

def mqdss5p_chal1_guessprobs_cumulative(field, r):
    """
    rv[w] = maximal probability of guessing at least w elements of ch_1
    
    sampling bias is accounted for
    """
    rv = list(itertools.repeat(None, r+1))
    exactprobs = mqdss5p_chal1_guessprobs_exact(field, r)
    w = r
    acc = 0
    while w >= 0:
        acc = acc + exactprobs[w]
        rv[w] = acc
        w = w - 1
        pass
    return rv

def mqdss5p_chal1_guessprobs_log2cum(field, r):
    "rv[w] = upper bound on log_2(prob of guessing at least w elems of ch_1)"
    return list(map(math.log2, mqdss5p_chal1_guessprobs_cumulative(field, r)))

# FIXME evaluation, 5-pass, step 2               

def mqdss5p_chal2_guessprob_orig(r, kzguess):
    assert r >= kzguess
    return -(r - kzguess)

def mqdss5p_chal2_guessprobs_orig(r):
    return [mqdss5p_chal2_guessprob_orig(r, kzg) for kzg in range(r+1)]

def mqdss5p_chal2_guessprob_fw(r0, r1, kzguess):
    r = r0 + r1
    return pfw_log2guessprob(r, r1, kzguess)

def mqdss5p_chal2_guessprobs_fw(r0, r1):
    r = r0 + r1
    return [mqdss5p_chal2_guessprob_fw(r0, r1, kzg) for kzg in range(r+1)]

# FIXME evaluation, 5-pass, loop to find security level               

def mqdss5p_kzseclevel_orig(field, r):
    ch1_lgps = mqdss5p_chal1_guessprobs_log2cum(field, r)
    ch2_lgps = mqdss5p_chal2_guessprobs_orig(r)
    return max(map(min, ch1_lgps, ch2_lgps))

def mqdss5p_kzseclevel_fw(field, r0, r1):
    r = r0 + r1
    ch1_lgps = mqdss5p_chal1_guessprobs_log2cum(field, r)
    ch2_lgps = mqdss5p_chal2_guessprobs_fw(r0, r1)
    return max(map(min, ch1_lgps, ch2_lgps))

# FIXME evaluation, 3-pass               

# FIXME 

# FIXME 













