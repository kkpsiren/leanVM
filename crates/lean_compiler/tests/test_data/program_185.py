from snark_lib import *

# An assignment in a match arm that returns does not block a later assignment
# to the same variable: the executed paths never overlap.


def main():
    z = Array(1)
    z[0] = 1
    c = z[0]
    x: Imm
    match c:
        case 0:
            x = 99
            return
        case 1:
            assert 0 == 0
    x = 3
    assert x == 3
    return
