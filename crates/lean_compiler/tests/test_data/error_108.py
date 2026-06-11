from snark_lib import *

# Error: `x` (forward-declared Mut) is reassigned inside a `range` loop —
# loop-carried mutables are unsupported. The check used to miss
# forward-declared mutables, and the loop's writes were silently discarded
# (the final assert read the stale pre-loop value 1 and passed).


def main():
    z = Array(1)
    z[0] = 0
    x: Mut
    if z[0] == 0:
        x = 1
    else:
        x = 2
    for i in range(0, 3):
        x = 99
    assert x == 1
    return
