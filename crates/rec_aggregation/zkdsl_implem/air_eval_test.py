from snark_lib import *
from utils import *
from hashing import *
from g8 import *

# Test entry: evaluate one table's generated AIR evaluator on hinted inputs and compare with a hinted
# expected value (computed natively by the Rust test).
N_EVALS = N_EVALS_PLACEHOLDER
N_ALPHAS = N_ALPHAS_PLACEHOLDER
N_BETAS = N_BETAS_PLACEHOLDER
N_TABLES_TEST = N_TABLES_PLACEHOLDER

EVALUATE_AIR_FUNCTIONS_PLACEHOLDER

def main():
    build_preamble_memory()
    evals = Array(DIM * N_EVALS)
    hint_witness("evals", evals)
    alphas = Array(DIM * N_ALPHAS)
    hint_witness("alphas", alphas)
    betas = Array(DIM * N_BETAS)
    hint_witness("betas", betas)
    expect = Array(DIM)
    hint_witness("expect", expect)
    tidx = Array(1)
    hint_witness("table_index", tidx)
    res = dispatch_eval(tidx[0], evals, alphas, betas)
    for i in unroll(0, DIM):
        assert res[i] == expect[i]
    return


# the same runtime dispatch as recursion.py's evaluate_air_constraints
def dispatch_eval(table_index, inner_evals, air_alpha_powers, logup_beta_eq_poly):
    res: Imm
    debug_assert(table_index < N_TABLES_TEST)
    match table_index:
        AIR_DISPATCH_ARMS_PLACEHOLDER
    return res
