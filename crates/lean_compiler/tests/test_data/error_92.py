# Error: len() on a scalar const-array element. The index is only constant after
# unroll substitution, so the check must also happen on the deferred path.
ARR = [11, 22]


def main():
    for i in unroll(0, 1):
        n = len(ARR[i])
        assert n == 0
    return
