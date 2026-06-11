from snark_lib import *

# Regression: same as program_188, with the mutable declared inside an unroll
# body (the renamed `__unrolled_*` mutables must be tracked by the
# constant-propagation guard).


def main():
    z = Array(1)
    z[0] = 1
    c = z[0]
    r = Array(1)
    for i in unroll(0, 1):
        x: Mut = 0
        x = 1
        if c == 1:
            x = 2
        r[i] = x
    assert r[0] == 2
    return
