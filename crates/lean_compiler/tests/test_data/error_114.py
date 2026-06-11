from snark_lib import *

# Error: a statement-position match_range whose lambda body is not a call
# would expand into bare no-effect expression statements.


def main():
    z = Array(1)
    z[0] = 0
    match_range(z[0], range(0, 3), lambda k: k + 1)
    return
