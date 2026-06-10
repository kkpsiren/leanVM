# Error: a parallel_range loop carries a mutable variable across iterations.
# The compiler buffers loop-carried mutables as `buff[i+1] = ...` read back as
# `buff[i]`, a cross-iteration dependency that parallel segments cannot observe.
# Parallel iterations must be independent, so this is rejected.
def main():
    total: Mut = 0
    for i in parallel_range(0, 4):
        total = total + i
    print(total)
    return
