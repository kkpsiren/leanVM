from snark_lib import *

# Error: match_range over an empty range would expand into a zero-arm match,
# which is not printable as intermediate source.


def main():
    z = Array(1)
    z[0] = 0
    y = match_range(z[0], range(0, 0), lambda k: k + 1)
    return
