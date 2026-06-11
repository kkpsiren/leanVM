from snark_lib import *

# Error: a value-returning @inline function is called as a bare statement
# (0 targets for 1 returned value). Must be a compile error, not a compiler
# panic.


def main():
    f(3)
    return

@inline
def f(c):
    return c + 1
