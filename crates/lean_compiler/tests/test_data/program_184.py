from snark_lib import *

# Regression test for early-exit detection in the mutable-variable SSA pass.
#
# A branch whose LAST statement is a `range` loop that runs zero iterations must
# be treated as falling through, even when the loop body always diverges
# (`assert False`). If `ends_with_early_exit` wrongly classifies the loop as a
# guaranteed exit, the then-branch is dropped from the phi-merge and the read
# after the `if` resolves to the wrong SSA version (here it would read 1 not 5).


def runtime(v):
    return v


def main():
    c = runtime(1)   # runtime 1, so the `if` is not constant-folded
    nn = runtime(0)  # runtime 0, so the inner loop runs zero times
    x: Mut = 0
    if c == 1:
        x = 1
        x = 5        # then-branch leaves x at a later version than else
        for j in range(0, nn):
            assert False
    else:
        x = 2
    assert x == 5    # then ran, inner loop ran 0x -> x must be 5
    print(x)
    return
