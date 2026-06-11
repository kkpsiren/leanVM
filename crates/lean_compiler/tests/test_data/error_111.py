from snark_lib import *

# Error: too many arguments to a const-specialized function. The extra
# argument used to be silently dropped (this program compiled and ran with
# x == 3).


def main():
    x = f(1, 2, 3)
    assert x == 3
    return

def f(a: Const, b):
    return a + b
