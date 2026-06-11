from snark_lib import *

# Error: after specializing with n = 0, every `return` of `f` is folded away
# and the body ends in a loop that may run zero times — the compiler cannot
# prove the function always returns (and must not append a reachable
# synthetic `return 0`).


def main():
    buf = Array(1)
    buf[0] = 0
    v = f(0, buf[0])
    return

def f(n: Const, m):
    if n == 0:
        for i in range(0, m):
            assert False
    else:
        return 1
