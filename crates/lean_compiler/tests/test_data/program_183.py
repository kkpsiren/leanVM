from snark_lib import *

# Regression test for the mutable-variable SSA pass. Branch conditions are loop
# iterators (genuinely runtime, so the if/match are NOT constant-folded), and
# mutable variables are reassigned inside the branches at equal and differing
# versions, including a nested if. Every accumulator is asserted, so a
# versioning / phi-merge bug surfaces as a failed assertion.


def main():
    # Runtime `if` inside a loop: `x` is reassigned in BOTH branches (same
    # version merges) and read after the if.
    total: Mut = 0
    for i in range(0, 5):
        x: Mut = 0
        if i == 2:
            x = 100
        else:
            x = i
        total = total + x
    assert total == 108  # 0 + 1 + 100 + 3 + 4

    # Runtime `match` on a loop iterator: arms reassign `m` a differing number of
    # times (phi over arms), with a nested if in one arm.
    macc: Mut = 0
    for j in range(0, 4):
        m: Mut = 0
        match j:
            case 0:
                m = 10
            case 1:
                m = 20
                m = m + 1
            case 2:
                if total == 108:
                    m = 30
                else:
                    m = 999
            case 3:
                m = 40
        macc = macc + m
    assert macc == 101  # 10 + 21 + 30 + 40

    print(total, macc)
    return
