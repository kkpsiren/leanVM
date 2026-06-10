# Error: an inner immutable declaration shadows an outer mutable variable of the
# same name. Name-based later passes cannot distinguish the shadow from the outer
# variable, so this must be rejected rather than silently miscompiled.
def choose(flag):
    x: Mut = 7
    if flag != 0:
        x: Imu
        x = 42
    return x

def main():
    y = choose(1)
    print(y)
    return
