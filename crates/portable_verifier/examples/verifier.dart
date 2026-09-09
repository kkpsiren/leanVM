// Dependency-free native Dart FFI adapter. This example has not been compiled with Dart.
// Supply DynamicLibrary.open(...) on Android/desktop; DynamicLibrary.process() for iOS static linking.
import 'dart:ffi';
import 'dart:typed_data';

typedef _AllocNative = Pointer<Uint8> Function(UintPtr);
typedef _FreeNative = Void Function(Pointer<Uint8>, UintPtr);
typedef _InitNative = Int32 Function(Pointer<Uint8>, UintPtr);
typedef _VerifyNative = Int32 Function(Pointer<Uint8>, UintPtr, Pointer<Uint8>, UintPtr, Pointer<Uint8>);

class NativeVerifier {
  final Pointer<Uint8> Function(int) _alloc;
  final void Function(Pointer<Uint8>, int) _free;
  final int Function(Pointer<Uint8>, int) _init;
  final int Function(Pointer<Uint8>, int, Pointer<Uint8>, int, Pointer<Uint8>) _verify;
  bool _ready = false;
  NativeVerifier(DynamicLibrary library)
      : _alloc = library.lookupFunction<_AllocNative, Pointer<Uint8> Function(int)>('fb_alloc'),
        _free = library.lookupFunction<_FreeNative, void Function(Pointer<Uint8>, int)>('fb_free'),
        _init = library.lookupFunction<_InitNative, int Function(Pointer<Uint8>, int)>('fb_init'),
        _verify = library.lookupFunction<_VerifyNative,
            int Function(Pointer<Uint8>, int, Pointer<Uint8>, int, Pointer<Uint8>)>('fb_verify') {
    final abi = library.lookupFunction<Uint32 Function(), int Function()>('fb_abi_version');
    if (abi() != 1) throw StateError('unsupported verifier ABI');
  }
  Pointer<Uint8> _copy(Uint8List bytes) {
    final p = _alloc(bytes.length);
    if (p == nullptr) throw StateError('allocation failed or size out of bounds');
    p.asTypedList(bytes.length).setAll(0, bytes);
    return p;
  }
  void initialize(Uint8List bytecodeCache) {
    final p = _copy(bytecodeCache);
    try {
      final code = _init(p, bytecodeCache.length);
      if (code != 0) throw StateError('initialization failed: $code');
      _ready = true;
    } finally { _free(p, bytecodeCache.length); }
  }
  // packedRows = pubkey[32] || digest[20], repeated in blob order, without signatures.
  bool verify(Uint8List envelope, Uint8List packedRows, Uint8List blobId) {
    if (!_ready) throw StateError('verifier is not ready');
    if (blobId.length != 32 || packedRows.isEmpty || packedRows.length % 52 != 0) {
      throw ArgumentError('invalid row or blob id dimensions');
    }
    final buffers = <(Pointer<Uint8>, int)>[];
    try {
      for (final bytes in [envelope, packedRows, blobId]) { buffers.add((_copy(bytes), bytes.length)); }
      final code = _verify(buffers[0].$1, envelope.length, buffers[1].$1, packedRows.length, buffers[2].$1);
      if (code == 4) _ready = false;
      if (code != 0 && code != 1) throw StateError('verifier ABI failure: $code');
      return code == 0;
    } finally { for (final b in buffers) { _free(b.$1, b.$2); } }
  }
}
