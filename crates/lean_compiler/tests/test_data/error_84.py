# Error: extension-op precompile size must be >= 1.
def main():
    a = Array(5)
    b = Array(5)
    res = Array(5)
    dot_product_ee(a, b, res, 0)
    return
