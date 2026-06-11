from snark_lib import *

# Error: same as error_118, through an `if` branch instead of a match arm.


def main():
    z = Array(1)
    z[0] = 0
    if z[0] == 0:
        t = Array(4)
        t[0] = 99
    t = 8
    x = t[0]
    assert x == 99
    return
