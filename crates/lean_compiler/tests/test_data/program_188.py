from snark_lib import *

# Regression: a mutable spliced in by inlining must not have its reads
# const-folded across a runtime branch (the renamed `__inlined_var_*` mutables
# must be tracked by the constant-propagation guard).


def main():
    z = Array(1)
    z[0] = 1
    c = z[0]
    r = pick(c)
    assert r == 2
    return

@inline
def pick(c):
    x: Mut = 0
    x = 1
    if c == 1:
        x = 2
    return x
