from snark_lib import *

# Error: too many arguments to an @inline function. The extra argument used to
# be silently dropped (this program compiled and ran with x == 6).


def main():
    x = g(5, 7)
    assert x == 6
    return

@inline
def g(a):
    return a + 1
