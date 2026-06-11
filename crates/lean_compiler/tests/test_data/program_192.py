from snark_lib import *

# Regression: a trailing loop may run zero times, so it must not count as a
# guaranteed early exit — the SSA unification has to keep the branch's final
# version (here x == 6, not the stale x == 5).


def main():
    buf = Array(2)
    buf[0] = 0
    buf[1] = 0
    c = buf[0]
    n = buf[1]
    x: Mut = 1
    if c == 0:
        x = 5
        x = 6
        for i in range(0, n):
            assert False
    else:
        x = 7
    assert x == 6
    return
