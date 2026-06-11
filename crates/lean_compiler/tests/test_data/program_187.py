from snark_lib import *

# Regression: an outer mutable written (before being read) inside an unroll
# body must keep its name across iterations instead of being renamed to a
# per-iteration local (which silently dropped the writes).


def main():
    y: Mut = 0
    for i in unroll(0, 2):
        y = i
    assert y == 1
    return
