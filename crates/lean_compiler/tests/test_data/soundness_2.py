from snark_lib import *


def main():
    p = 0
    mode = p[0]
    x = p[1]
    y = p[2]
    expected = p[3]

    computed: Imm
    match mode:
        case 0:
            computed = add_op(x, y)
        case 1:
            computed = sub_op(x, y)
        case 2:
            computed = mul_op(x, y)
        case 3:
            computed = combined(x, y)
    assert computed == expected
    return


def add_op(a, b):
    return a + b


def sub_op(a, b):
    return a - b


def mul_op(a, b):
    return a * b


def combined(a, b):
    return mul_op(a, b) + add_op(a, b)
