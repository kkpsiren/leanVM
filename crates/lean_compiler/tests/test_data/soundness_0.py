from snark_lib import *


def main():
    p = 0
    a = p[0]
    b = p[1]
    c = p[2]
    d = p[3]

    assert double(a) == b
    assert square_plus_one(a) == c
    assert a + d == 10
    return


@inline
def double(x):
    return x + x


def square_plus_one(x):
    return x * x + 1
