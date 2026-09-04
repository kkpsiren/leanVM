from snark_lib import *
from utils import *
from hashing import *
from g8 import *

# Test entry: evaluate one table's generated AIR evaluator on hinted inputs and compare with a hinted
# expected value (computed natively by the Rust test).
N_EVALS = N_EVALS_PLACEHOLDER
N_ALPHAS = N_ALPHAS_PLACEHOLDER
N_BETAS = N_BETAS_PLACEHOLDER
N_TABLES_TEST = 9

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
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 3:
            res = evaluate_air_constraints_table_3(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 4:
            res = evaluate_air_constraints_table_4(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 5:
            res = evaluate_air_constraints_table_5(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 6:
            res = evaluate_air_constraints_table_6(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 7:
            res = evaluate_air_constraints_table_7(inner_evals, air_alpha_powers, logup_beta_eq_poly)
        case 8:
            res = evaluate_air_constraints_table_8(inner_evals, air_alpha_powers, logup_beta_eq_poly)
    return res
