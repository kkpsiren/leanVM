from snark_lib import *

# Error: user code calls a compiler-generated `__` name directly. This used
# to compile and run (binding to the order-dependent specialization of
# `scaled`), defeating the reserved-namespace guarantee.


def main():
    z = Array(1)
    z[0] = 3
    a = scaled(z[0], 2)
    assert a == 6
    b = __spec0_scaled_k_2(z[0])
    assert b == 6
    return

def scaled(x, k: Const):
    return x * k
