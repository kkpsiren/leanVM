#ifndef FB_VERIFIER_H
#define FB_VERIFIER_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* ABI v1. All calls on one library/instance must be serialized.
 * Status: 0 success, 1 rejected, 2 invalid argument, 3 uninitialized,
 * 4 native panic/poisoned, 5 already initialized. Wasm panics trap instead;
 * discard that instance. A trap, exception, or nonzero status is NEVER acceptance.
 * Buffers must be valid and immutable for each call. No ownership is transferred.
 * fb_free takes exactly the pointer and size returned/requested by fb_alloc, once.
 * Native invalid/dangling pointers are undefined behavior, as with ordinary C APIs.
 */
uint32_t fb_abi_version(void);
uint8_t *fb_alloc(size_t size); /* 1..32 MiB, NULL outside bounds */
void fb_free(uint8_t *pointer, size_t size);
/* Prefer the FBVK0001 verifier artifact: every byte is SHA-512 authenticated against a
 * release pin linked offline to the original Poseidon VK. Legacy instruction caches
 * remain supported through reconstruction and a full Poseidon hash check (slow).
 * The input may be freed after initialization; the library owns its immutable table.
 */
int32_t fb_init(const uint8_t *bytecode_cache, size_t size); /* immutable pinned VK, once */
/* Envelope v3; rows are contiguous pubkey[32] || digest[20] in blob order.
 * blob_id is independently obtained by the reader, exactly 32 bytes.
 * At most 16 MiB envelope and 32 MiB row bytes. No signatures are needed.
 */
int32_t fb_verify(const uint8_t *envelope, size_t envelope_size,
                  const uint8_t *rows, size_t rows_size, const uint8_t *blob_id);
/* Requested live/peak Rust heap bytes: excludes allocator overhead, stack and runtime.
 * Reset sets the peak to current live bytes. These are process-wide for a native library.
 */
size_t fb_heap_live(void);
size_t fb_heap_peak(void);
void fb_heap_reset_peak(void);
#ifdef __cplusplus
}
#endif
#endif
