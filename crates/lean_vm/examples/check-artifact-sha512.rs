//! No proofs: cross-check this output against an independent host SHA-512 implementation.
use lean_vm::ed25519::sha512_table::sha512_bytes;
fn main() {
    for n in [0, 1, 3, 110, 111, 112, 113, 127, 128, 129, 239, 240, 255, 256, 257, 1024, 1_000_000] {
        let bytes: Vec<u8> = (0..n).map(|i| ((i * 131 + 17) % 256) as u8).collect();
        let digest = sha512_bytes(&bytes);
        println!("{n} {}", digest.iter().map(|b| format!("{b:02x}")).collect::<String>());
    }
}
