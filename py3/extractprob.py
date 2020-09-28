
# Authors: Robert Ransom

# This software is released to the public domain.

# To the extent permitted by law, this software is provided WITHOUT ANY
# WARRANTY WHATSOEVER.

import math
import fractions
import itertools

import pqsigparam.common

log2 = pqsigparam.common.log2
binom = pqsigparam.common.binom

def q2_uniform_iid_extfailprob_log2(field, r):
    q = field.q
    prob_oneround = fractions.Fraction(3*q + 1, 4*q)
    return log2(prob_oneround)*r

def number_of_fwv_pairs(n, w1, w2):
    return binom(n, w1) * binom(n, w2)

def number_of_fwv_pairs_intersecting(n, w1, w2, k):
    return (binom(n, k) *
            binom((n-k), (w1-k) + (w2-k)) *
            binom((w1-k) + (w2-k), (w1-k)))

def number_of_fwv_pairs_differing(n, w1, w2, kprime):
    # (w1 - k) + (w2 - k) = kprime
    k2 = w1 + w2 - kprime
    if (k2 % 2) != 0:
        return 0
    else:
        return number_of_fwv_pairs_intersecting(n, w1, w2, k2 // 2)
    pass

def test_fwv_pair_counts(n, w1, w2):
    npairs = number_of_fwv_pairs(n, w1, w2)
    npairs2 = sum(number_of_fwv_pairs_intersecting(n, w1, w2, k)
                  for k in range(n))
    npairs3 = sum(number_of_fwv_pairs_differing(n, w1, w2, k)
                  for k in range(n))
    assert(npairs == npairs2)
    assert(npairs == npairs3)

def prob_fwv_pairs_intersecting(n, w1, w2, k):
    return fractions.Fraction(number_of_fwv_pairs_intersecting(n, w1, w2, k),
                              number_of_fwv_pairs(n, w1, w2))

def prob_fwv_pairs_differing(n, w1, w2, k):
    return fractions.Fraction(number_of_fwv_pairs_differing(n, w1, w2, k),
                              number_of_fwv_pairs(n, w1, w2))

def q2_ctver_extsuccprob_pass2_nodiverg(r, r1, k, diffdist):
    "prob of 4 pass-2 challenge vectors allowing extraction in exactly k runs"
    rv = 0
    for d1 in range(r):
        for d2 in range(r):
            rv += (prob_fwv_pairs_intersecting(r, d1, d2, k) *
                   diffdist[d1] * diffdist[d2])
            pass
        pass
    return rv

def q2_ctver_extfailprob_pass1(field):
    Pmax = field.sampling_max_preimages()
    denom = (1 << field.sampling_bits)
    pmax = fractions.Fraction(Pmax, denom)
    return pmax

def q2_ctver_extfailprob_nodiverg(field, r, r1):
    diffdist = [prob_fwv_pairs_differing(r, r1, r1, d) for d in range(r)]
    pmax = q2_ctver_extfailprob_pass1(field)
    acc = 0
    for k in range(r):
        acc += (pmax**(2*k)) * q2_ctver_extsuccprob_pass2_nodiverg(r, r1, k, diffdist)
        pass
    return acc

def q2_ctver_extfailprob_log2(field, r, r1):
    log2diverg = pqsigparam.common.log2diverg_sorting(r, 31)
    return log2(q2_ctver_extfailprob_nodiverg(field, r, r1)) + log2diverg

