from snark_lib import *


def main():
    p = 0
    expected_sum = p[0]
    x = p[1]
    expected_pipeline = p[2]
    flag = p[3]

    markers = Array(5)
    for i in unroll(0, 5):
        markers[i] = i

    sum_buf = Array(6)
    sum_buf[0] = 0
    for i in range(0, 5):
        m = markers[i]
        s: Mut = sum_buf[i]
        if m == 0:
            s = s + 10
        else:
            s = s + m
        sum_buf[i + 1] = s
    assert sum_buf[5] == expected_sum

    assert pipeline(x, x) == expected_pipeline

    if flag == 1:
        assert expected_sum < 50
    else:
        assert expected_sum == 0

    assert flag * (1 - flag) == 0
    return


@inline
def pipeline(a, b):
    return wrapper(a, b) + a


def wrapper(a, b):
    return inner(a, b) + b


@inline
def inner(a, b):
    return a * b
