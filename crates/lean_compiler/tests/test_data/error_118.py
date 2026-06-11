from snark_lib import *

# Error: `t` is reassigned after the match (the arm's `Array` binding must not
# leak past the match either — this program used to compile and execute with
# `x` reading the arm's dead const-malloc slot).


def main():
    z = Array(1)
    z[0] = 0
    match z[0]:
        case 0:
            t = Array(4)
            t[0] = 99
    t = 8
    x = t[0]
    assert x == 99
    return
