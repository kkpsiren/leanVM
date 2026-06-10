from snark_lib import *


def main():
    p = 0
    seed = p[0]
    last_write = p[1]
    match_tally = p[2]
    alt = p[3]

    counter_buf = Array(5)
    counter_buf[0] = 0
    for i in range(0, 4):
        counter_buf[i + 1] = 2 * i + 1
    assert counter_buf[4] == last_write

    acc_buf = Array(5)
    acc_buf[0] = seed
    for i in range(0, 4):
        a: Mut = acc_buf[i]
        match i:
            case 0:
                a = a + 1
            case 1:
                a = a + 3
            case 2:
                a = a + 5
            case 3:
                a = a + 7
        acc_buf[i + 1] = a
    assert acc_buf[4] == match_tally

    chosen: Imm
    if seed == 0:
        chosen = 0
    else:
        chosen = seed * 2
    assert chosen == alt
    return
