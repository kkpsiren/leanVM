from snark_lib import *
from utils import *

# Loop-based evaluation of the ed25519 G8 limb identity (lean_vm gadgets.rs::eval_identity) at a point:
#   v = Σ ±a·b (limb convolution) + Σ ±c − r − (q − 128)·M ;  constraint_i = gate · (v_i − W'_{i−1} + 256·W'_i)
# with W' = w − 2^15, i in 0..65, w_i = 0 for i ≥ 64. All values are extension-field elements (DIM cells).
# Memory is write-once, so every step returns a fresh 65-limb buffer.
G8_LIMBS = 32
G8_QL = 34
G8_WL = 64
G8_NV = 65
G8_Q_OFFSET = 128
G8_W_OFFSET = 32768


def g8_zero():
    v = Array(DIM * G8_NV)
    for i in unroll(0, G8_NV):
        set_to_5_zeros(v + i * DIM)
    return v


def g8_rev(b):
    r = Array(DIM * G8_LIMBS)
    for i in unroll(0, G8_LIMBS):
        copy_ef(b + (G8_LIMBS - 1 - i) * DIM, r + i * DIM)
    return r


# v_out[i] = v[i] ± Σ_j a[j]·b[i−j]  (b given reversed: b_rev[k] = b[31−k])
def g8_conv_add(v, a, b_rev):
    out = Array(DIM * G8_NV)
    for i in unroll(0, 63):
        t = Array(DIM)
        if i < 32:
            dot_product_ee(a, b_rev + (31 - i) * DIM, t, i + 1)
        else:
            dot_product_ee(a + (i - 31) * DIM, b_rev, t, 63 - i)
        add_ee(v + i * DIM, t, out + i * DIM)
    copy_ef(v + 63 * DIM, out + 63 * DIM)
    copy_ef(v + 64 * DIM, out + 64 * DIM)
    return out


def g8_conv_sub(v, a, b_rev):
    out = Array(DIM * G8_NV)
    for i in unroll(0, 63):
        t = Array(DIM)
        if i < 32:
            dot_product_ee(a, b_rev + (31 - i) * DIM, t, i + 1)
        else:
            dot_product_ee(a + (i - 31) * DIM, b_rev, t, 63 - i)
        sub_extension(v + i * DIM, t, out + i * DIM)
    copy_ef(v + 63 * DIM, out + 63 * DIM)
    copy_ef(v + 64 * DIM, out + 64 * DIM)
    return out


def g8_lin_add(v, c):
    out = Array(DIM * G8_NV)
    for i in unroll(0, G8_LIMBS):
        add_ee(v + i * DIM, c + i * DIM, out + i * DIM)
    for i in unroll(G8_LIMBS, G8_NV):
        copy_ef(v + i * DIM, out + i * DIM)
    return out


def g8_lin_sub(v, c):
    out = Array(DIM * G8_NV)
    for i in unroll(0, G8_LIMBS):
        sub_extension(v + i * DIM, c + i * DIM, out + i * DIM)
    for i in unroll(G8_LIMBS, G8_NV):
        copy_ef(v + i * DIM, out + i * DIM)
    return out


# v_out[i] = v[i] − Σ_{j+k=i} (q[j] − 128)·M[k]  (q: 34 limbs, M: 32 base limbs given reversed: m_rev[t] = M[31−t])
def g8_qsub(v, q, m_rev):
    qoff = Array(DIM * G8_QL)
    for j in unroll(0, G8_QL):
        qoff[j * DIM] = q[j * DIM] - G8_Q_OFFSET
        for d in unroll(1, DIM):
            qoff[j * DIM + d] = q[j * DIM + d]
    out = Array(DIM * G8_NV)
    for i in unroll(0, G8_NV):
        t = Array(DIM)
        if i < 32:
            dot_product_be(m_rev + (31 - i), qoff, t, i + 1)
        elif i < 34:
            dot_product_be(m_rev, qoff + (i - 31) * DIM, t, 32)
        else:
            dot_product_be(m_rev, qoff + (i - 31) * DIM, t, 65 - i)
        sub_extension(v + i * DIM, t, out + i * DIM)
    return out


# out[i] = gate · (v[i] − W'[i−1] + 256·W'[i]),  W' = w − 2^15 (64 limbs), W'[−1] = W'[64] = 0
def g8_chain(out, gate, v, w):
    woff = Array(DIM * G8_WL)
    for j in unroll(0, G8_WL):
        woff[j * DIM] = w[j * DIM] - G8_W_OFFSET
        for d in unroll(1, DIM):
            woff[j * DIM + d] = w[j * DIM + d]
    for i in unroll(0, G8_NV):
        t: Imm
        if i == 0:
            t = add_extension_ret(v, mul_base_extension_ret(256, woff))
        elif i < G8_WL:
            t = add_extension_ret(sub_extension_ret(v + i * DIM, woff + (i - 1) * DIM), mul_base_extension_ret(256, woff + i * DIM))
        else:
            t = sub_extension_ret(v + i * DIM, woff + (i - 1) * DIM)
        mul_extension(gate, t, out + i * DIM)
    return
