from snark_lib import *

# Error: one match arm assigns `t` while a sibling arm reads the enclosing
# `t` — ambiguous, and rejected as a reassignment of the loop argument. This
# used to panic the compiler ("Variable t not in scope") because the sibling
# arm's read was misclassified as loop-internal.


def main():
    t = 5
    z = Array(2)
    z[0] = 0
    z[1] = 1
    for i in range(0, 2):
        match z[i]:
            case 0:
                t = 1
                print(t)
            case 1:
                print(t)
    return
