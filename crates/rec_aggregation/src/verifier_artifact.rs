//! Trusted release linkage: the dictionary artifact expands to the table with VK_HASH.
//! Reproduce with `export-verifier-artifact`; never obtain these pins from an untrusted manifest.
pub const VK_HASH: [u32; 8] = [1153961582, 1250141101, 1638904970, 1982146112,
    763994888, 2126617202, 1686598344, 1973457087];
// FBVK0001: 20,809,504 bytes; 346,149 dictionary rows and 1,048,576 row indices.
// SHA-512 19c13a67d88ba99bb553f282c9d1b9cbffcb9327a8d2fef0abe2bfa4bd0e0280
//         0b74acc547ede847b94275d27e170b9cd7d4214f18afa9d16f541365be0fdb4e
pub const ARTIFACT_SHA512: [u8; 64] = [
    25, 193, 58, 103, 216, 139, 169, 155, 181, 83, 242, 130, 201, 209, 185, 203,
    255, 203, 147, 39, 168, 210, 254, 240, 171, 226, 191, 164, 189, 14, 2, 128,
    11, 116, 172, 197, 71, 237, 232, 71, 185, 66, 117, 210, 126, 23, 11, 156,
    215, 212, 33, 79, 24, 175, 169, 209, 111, 84, 19, 101, 190, 15, 219, 78,
];
