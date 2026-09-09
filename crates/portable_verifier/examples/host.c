#define _POSIX_C_SOURCE 200809L
#include "fb_verifier.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct { uint8_t *p; size_t n; } Buffer;
static Buffer load(const char *name) {
    FILE *f = fopen(name, "rb"); if (!f) { perror(name); exit(1); }
    if (fseek(f, 0, SEEK_END)) exit(1);
    long n = ftell(f); if (n <= 0 || n > 32 * 1024 * 1024) exit(1);
    rewind(f); Buffer b = {fb_alloc((size_t)n), (size_t)n};
    if (!b.p || fread(b.p, 1, b.n, f) != b.n) exit(1);
    fclose(f); return b;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static void expect(const char *name, int actual, int wanted) {
    printf("%s: %d\n", name, actual);
    if (actual != wanted) exit(1);
}
int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: host bytecode.bin envelope.bin rows.bin blob-id.bin\n"); return 2; }
    Buffer bc=load(argv[1]), env=load(argv[2]), rows=load(argv[3]), id=load(argv[4]);
    if (id.n != 32) return 2;
    expect("ABI", fb_abi_version(), 1);
    expect("uninitialized", fb_verify(env.p,env.n,rows.p,rows.n,id.p), 3);
    double t=now(); expect("init",fb_init(bc.p,bc.n),0);
    printf("init_ms: %.3f; heap_peak: %zu\n", (now()-t)*1000,fb_heap_peak());
    fb_free(bc.p,bc.n);
    for (int i=0;i<3;i++) {
        fb_heap_reset_peak(); t=now(); expect("golden",fb_verify(env.p,env.n,rows.p,rows.n,id.p),0);
        printf("verify_ms: %.3f; heap_live: %zu; heap_peak: %zu\n", (now()-t)*1000,fb_heap_live(),fb_heap_peak());
    }
    rows.p[32]^=1; expect("tampered row",fb_verify(env.p,env.n,rows.p,rows.n,id.p),1); rows.p[32]^=1;
    env.p[env.n-1]^=1; expect("tampered proof",fb_verify(env.p,env.n,rows.p,rows.n,id.p),1); env.p[env.n-1]^=1;
    expect("truncated envelope",fb_verify(env.p,env.n-1,rows.p,rows.n,id.p),1);
    expect("golden after rejects",fb_verify(env.p,env.n,rows.p,rows.n,id.p),0);
    fb_free(env.p,env.n); fb_free(rows.p,rows.n); fb_free(id.p,id.n);
    return 0;
}
