from snark_lib import *

# Error: `x` is assigned in a fall-through match arm and reassigned after the
# match (same frame slot). This used to be accepted because the pre-match
# `assigned` snapshot was restored after the arms; the executed path here
# (case 0) never writes twice, so the program even ran successfully.


def main():
    z = Array(1)
    z[0] = 0
    c = z[0]
    x: Imm
    match c:
        case 0:
            assert 0 == 0
        case 1:
            x = 2
    x = 3
    assert x == 3
    return
