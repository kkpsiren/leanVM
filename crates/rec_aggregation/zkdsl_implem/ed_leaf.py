from snark_lib import *
from utils import *

# ed25519 leaf driver (Phase D transcript v1) as a mode of the recursion program. Kept in sync with
# lean_prover::ed25519_leaf::LEAF_PROGRAM (the standalone program used by the leaf tests).

DOMAIN_ROOT = DOMAIN_ROOT_PLACEHOLDER
DOMAIN_CTX = DOMAIN_CTX_PLACEHOLDER
DOMAIN_RHO = DOMAIN_RHO_PLACEHOLDER
BPT = BPT_PLACEHOLDER

def pack11(src, dst):
    for k in unroll(0, 10):
        dst[k] = src[3 * k] + 256 * src[3 * k + 1] + 65536 * src[3 * k + 2]
    dst[10] = src[30] + 256 * src[31]
    return

def pack7(src, dst):
    for k in unroll(0, 6):
        dst[k] = src[3 * k] + 256 * src[3 * k + 1] + 65536 * src[3 * k + 2]
    dst[6] = src[18] + 256 * src[19]
    return

def ed25519_leaf(n, meta, root_expected):
    cols = Array(52 * n)
    hint_witness("cols", cols)
    q = Array(64 * n)
    hint_witness("q", q)
    s = Array(32 * n)
    hint_witness("s", s)
    gstart = Array(n)
    hint_witness("gstart", gstart)
    qa = Array(64 * n)
    hint_witness("qa", qa)
    zeros = Array(64)
    for t in unroll(0, 64):
        zeros[t] = 0
    bpt = Array(97)
    for t in unroll(0, 97):
        bpt[t] = BPT[t]

    # ---- root over the columns
    rst = Array(16 * (3 * n + 1))
    ivr = Array(8)
    ivr[0] = DOMAIN_ROOT
    for t in unroll(1, 8):
        ivr[t] = 0
    hdr = Array(8)
    hdr[0] = n
    for t in unroll(1, 8):
        hdr[t] = 0
    poseidon16_permute(ivr, hdr, rst)
    for i in range(0, n):
        apk = Array(11)
        pack11(cols + 52 * i, apk)
        dpk = Array(7)
        pack7(cols + 52 * i + 32, dpk)
        c0 = Array(8)
        c1 = Array(8)
        c2 = Array(8)
        for t in unroll(0, 8):
            c0[t] = apk[t]
        for t in unroll(0, 3):
            c1[t] = apk[8 + t]
        for t in unroll(0, 5):
            c1[3 + t] = dpk[t]
        c2[0] = dpk[5]
        c2[1] = dpk[6]
        for t in unroll(2, 8):
            c2[t] = 0
        poseidon16_permute(rst + 16 * (3 * i), c0, rst + 16 * (3 * i + 1))
        poseidon16_permute(rst + 16 * (3 * i + 1), c1, rst + 16 * (3 * i + 2))
        poseidon16_permute(rst + 16 * (3 * i + 2), c2, rst + 16 * (3 * i + 3))
    root = rst + 16 * (3 * n) + 8

    # ---- the root is public (leaf input data); H_leaf is the framework's hash of the input data
    for t in unroll(0, 8):
        assert root[t] == root_expected[t]

    # ---- R records (torsion certificates R = 8Q)
    rrec = Array(97 * n)
    for i in range(0, n):
        ed_sig(q + 64 * i, rrec + 97 * i, 0)

    # ---- ctx sponge: root, meta, then (R packed, s packed) per signature
    cst = Array(16 * (3 * n + 2))
    ivc = Array(8)
    ivc[0] = DOMAIN_CTX
    for t in unroll(1, 8):
        ivc[t] = 0
    poseidon16_permute(ivc, root, cst)
    poseidon16_permute(cst, meta, cst + 16)
    for i in range(0, n):
        rb = Array(32)
        for t in unroll(0, 31):
            rb[t] = rrec[97 * i + 32 + t]
        rb[31] = rrec[97 * i + 63] + 128 * rrec[97 * i + 64]
        rpk = Array(11)
        pack11(rb, rpk)
        spk = Array(11)
        pack11(s + 32 * i, spk)
        c0 = Array(8)
        c1 = Array(8)
        c2 = Array(8)
        for t in unroll(0, 8):
            c0[t] = rpk[t]
        for t in unroll(0, 3):
            c1[t] = rpk[8 + t]
        for t in unroll(0, 5):
            c1[3 + t] = spk[t]
        for t in unroll(0, 6):
            c2[t] = spk[5 + t]
        c2[6] = 0
        c2[7] = 0
        poseidon16_permute(cst + 16 * (3 * i + 1), c0, cst + 16 * (3 * i + 2))
        poseidon16_permute(cst + 16 * (3 * i + 2), c1, cst + 16 * (3 * i + 3))
        poseidon16_permute(cst + 16 * (3 * i + 3), c2, cst + 16 * (3 * i + 4))
    ctx = cst + 16 * (3 * n + 1) + 8

    # ---- rho_i = P(ctx, [i, DOMAIN_RHO, 0..])[8..12]
    rho = Array(16 * n)
    for i in range(0, n):
        rin = Array(8)
        rin[0] = i
        rin[1] = DOMAIN_RHO
        for t in unroll(2, 8):
            rin[t] = 0
        poseidon16_permute(ctx, rin, rho + 16 * i)

    # ---- per-signature pipeline with hinted signer groups
    assert gstart[0] == 1
    gk = Array(n + 1)
    gk[0] = 0
    arec = Array(97 * n)
    qarec = Array(97 * n)
    blk = Array(128 * n)
    rec = Array(101 * n)
    out = Array(90 * n)
    sacc = Array(64 * n)
    krec = Array(34 * n)
    kout = Array(84 * n)
    for i in range(0, n):
        g = gstart[i]
        assert g * (g - 1) == 0
        if g == 1:
            gk[i + 1] = i
            ed_decompress(cols + 52 * i, arec + 97 * i, 0)
            ed_sig(qa + 64 * i, qarec + 97 * i, 0)
            for t in unroll(0, 64):
                assert arec[97 * i + t] == qarec[97 * i + t]
            for t in unroll(0, 32):
                sacc[64 * i + t] = 0
            if i == 0:
                for t in unroll(0, 32):
                    sacc[64 * i + 32 + t] = 0
            else:
                for t in unroll(0, 32):
                    sacc[64 * i + 32 + t] = out[90 * (i - 1) + 32 + t]
                for t in unroll(0, 32):
                    krec[34 * i + t] = out[90 * (i - 1) + t]
                krec[34 * i + 32] = arec + 97 * gk[i]
                krec[34 * i + 33] = 1
                signer_scalar(krec + 34 * i, kout + 84 * i, 0)
        else:
            gk[i + 1] = gk[i]
            for t in unroll(0, 32):
                assert cols[52 * i + t] == cols[52 * gk[i] + t]
        for t in unroll(0, 31):
            blk[128 * i + t] = rrec[97 * i + 32 + t]
        blk[128 * i + 31] = rrec[97 * i + 63] + 128 * rrec[97 * i + 64]
        for t in unroll(0, 32):
            blk[128 * i + 32 + t] = cols[52 * i + t]
        for t in unroll(0, 20):
            blk[128 * i + 64 + t] = cols[52 * i + 32 + t]
        blk[128 * i + 84] = 128
        for t in unroll(85, 126):
            blk[128 * i + t] = 0
        blk[128 * i + 126] = 2
        blk[128 * i + 127] = 160
        sha512(blk + 128 * i, rec + 101 * i, zeros)
        for t in unroll(0, 32):
            rec[101 * i + 64 + t] = s[32 * i + t]
        for t in unroll(0, 4):
            rec[101 * i + 96 + t] = rho[16 * i + 8 + t]
        rec[101 * i + 100] = rrec + 97 * i
        if g == 1:
            scalar_l(rec + 101 * i, sacc + 64 * i, out + 90 * i)
        else:
            scalar_l(rec + 101 * i, out + 90 * (i - 1), out + 90 * i)
    # ---- close the last group and the S row
    lk = Array(34)
    for t in unroll(0, 32):
        lk[t] = out[90 * (n - 1) + t]
    lk[32] = arec + 97 * gk[n]
    lk[33] = 1
    lkout = Array(84)
    signer_scalar(lk, lkout, 0)
    srec = Array(34)
    for t in unroll(0, 32):
        srec[t] = out[90 * (n - 1) + 32 + t]
    srec[32] = bpt
    srec[33] = 0
    sout = Array(84)
    signer_scalar(srec, sout, 0)
    return
