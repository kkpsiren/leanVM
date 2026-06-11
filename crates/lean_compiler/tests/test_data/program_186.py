from snark_lib import *

# Regression: the const-specialization key must be unambiguous. The (name,
# const-arg-name) concatenations of `compute(log_n=5)` and `compute_log(n=5)`
# collide if joined with `_`, silently routing the second call to the first
# function's specialization.


def main():
    a = compute(5)
    b = compute_log(5)
    assert a == 500
    assert b == 15
    return

def compute(log_n: Const):
    return log_n * 100

def compute_log(n: Const):
    return n * 3
