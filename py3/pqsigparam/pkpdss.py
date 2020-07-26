
import math
import functools
import collections

import pqsigparam.common

# signature component size sets

f251 = pqsigparam.common.FieldParams(251, 16)
f509 = pqsigparam.common.FieldParams(509, 16)
f4093 = pqsigparam.common.FieldParams(4093, 16)

f977 = pqsigparam.common.FieldParams(977, 16)
f997 = pqsigparam.common.FieldParams(997, 16)
f1409 = pqsigparam.common.FieldParams(1409, 16)
f1889 = pqsigparam.common.FieldParams(1889, 16)

#class PKPKeyParams(object):
#    __slots__ = ('field', 'n', 'm', 'seedbytes')
#    def __init__(self, field, n, m, seedbytes):
#        self.field = field
#        self.n = n
#        self.m = m
#        self.seedbytes = seedbytes
#        pass
#    pass

vector_encode_limit = 16384
def VectorEncode(R, M):
    if len(M) == 0:
        return []
    S = []
    if len(M) == 1:
        r, m = R[0], M[0]
        while m > 1:
            S += [r%256]
            r, m = r//256, (m+255)//256
            pass
        return S
    R2, M2 = [], []
    for i in range(0, len(M) - 1, 2):
        m, r = M[i]*M[i+1], R[i] + M[i]*R[i+1]
        while m >= vector_encode_limit:
            S += [r%256]
            r, m = r//256, (m+255)//256
            pass
        R2 += [r]
        M2 += [m]
        pass
    if len(M) & 1:
        R2 += [R[-1]]
        M2 += [M[-1]]
        pass
    return S + VectorEncode(R2, M2)

@functools.lru_cache()
def vector_encode_bytes(count, mod):
    return len(VectorEncode([0]*count, [mod]*count))

PKPKeyParams = collections.namedtuple('PKPKeyParams', ('field', 'n', 'm', 'seedbytes', 'hashbytes'))

kp251c1 = PKPKeyParams(f251, 69, 41, 16, 32)
kp251c2 = PKPKeyParams(f251, 69, 41, 24, 32)
kp509c3 = PKPKeyParams(f509, 94, 54, 24, 48)
kp509c4 = PKPKeyParams(f509, 94, 54, 32, 48)
kp4093c5 = PKPKeyParams(f4093, 106, 47, 32, 64)

kp977c1 = PKPKeyParams(f977, 61, 28, 16, 32)
kp977n64c1 = PKPKeyParams(f977, 64, 28, 16, 32)
kp997c1 = PKPKeyParams(f997, 61, 28, 16, 32)
kp997n64c1 = PKPKeyParams(f997, 64, 30, 16, 32)
kp997c2 = PKPKeyParams(f997, 61, 28, 24, 32)
kp1409c3 = PKPKeyParams(f1409, 87, 42, 24, 48)
kp1409c4 = PKPKeyParams(f1409, 87, 42, 32, 48)
kp1889c5 = PKPKeyParams(f1889, 111, 55, 32, 64)

class PKPFormatParams(object):
    def nvect_perm_bytes(self, kp):
        return self.nvect_bytes(kp) + self.perm_bytes(kp)
    pass
class PKPFormatParamsLoose(PKPFormatParams):
    def nvect_bytes(self, kp):
        return math.ceil(math.ceil(math.log2(kp.field.q)) * kp.n / 8)
    def perm_bytes(self, kp):
        return vector_encode_bytes(kp.n, kp.n)
    pass
class PKPFormatParamsSemiLoose(PKPFormatParamsLoose):
    def nvect_bytes(self, kp):
        return vector_encode_bytes(kp.n, kp.field.q)
    pass
class PKPFormatParamsTight(PKPFormatParamsSemiLoose):
    def perm_bytes(self, kp):
        return math.ceil(math.log2(math.factorial(kp.n)) / 8)
    pass

fploose = PKPFormatParamsLoose()
fpsemiloose = PKPFormatParamsSemiLoose()
fptight = PKPFormatParamsTight()

def evaluate_sigsize(kp, sp, fp, r0, r1):
    r = r0 + r1
    rv  =         kp.hashbytes          # R
    rv +=         sp.hashbytes          # H(initial commitments)
    # ch_1 computed from preceding hash
    rv +=         sp.hashbytes          # ch_2
    rv += r0 *    kp.seedbytes          # rho_0      for each round with ch_2=0
    rv += r1 * fp.nvect_perm_bytes(kp)  # (z, sigma) for each round with ch_2=1
    rv += r  *    sp.hashbytes          # c_(1-b)    for each round   (b=ch_2)
    return rv


