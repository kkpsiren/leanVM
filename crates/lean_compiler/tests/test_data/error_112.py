from snark_lib import *

# Error: the extension-op length argument is a runtime value. Must be a
# compile error, not a compiler panic.


def main():
    z = Array(1)
    z[0] = 2
    n = z[0]
    a = Array(20)
    b = Array(20)
    r = Array(5)
    dot_product_ee(a, b, r, n)
    return
