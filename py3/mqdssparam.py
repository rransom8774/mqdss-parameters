
import sys
import math
import operator
import functools
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
    def log2diverg_vector(self, n):
        # DJB divergence-20180430, Theorem 2.1
        # divergence <= (Pq/(2**b))**n
        # P = # of preimages; P <= ceil((2**b)/q) by Theorems 2.2 and 2.3
        if self.log2diverg1 == None:
            q = self.q
            b = self.sampling_bits
            P = (2**b) // q   # NOTE floor division
            if (2**b) % q != 0:
                P += 1
                pass
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



# FIXME evaluation, 5-pass, step 1               

# FIXME evaluation, 5-pass, step 2               

# FIXME evaluation, 5-pass, loop to find KZ loss               

# FIXME evaluation, 3-pass               

# FIXME 

# FIXME 













