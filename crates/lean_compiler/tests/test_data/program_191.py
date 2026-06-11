from snark_lib import *

# Match arms mixing arm-local variables with reads of enclosing-scope
# variables: the loop -> recursion lowering must classify `t` as external
# (passed as an argument) even though one arm declares a local of its own.


def main():
    t = 7
    z = Array(2)
    z[0] = 0
    z[1] = 1
    out = Array(2)
    for i in range(0, 2):
        match z[i]:
            case 0:
                u = t + 1
                out[i] = u
            case 1:
                out[i] = t
    assert out[0] == 8
    assert out[1] == 7
    return
