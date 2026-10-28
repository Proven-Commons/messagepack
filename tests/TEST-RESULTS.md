# Test results: messagepack

Seed: 20261026. Tool: the Lean command line program, one process per section, requests batched.

Python's `msgpack` library was importable in the interpreter that ran this harness (version 1.2.3); the library differential ran.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases from the spec (every family and width) | 39 | 39 |
| Integer width boundaries and length form steps | 84 | 84 |
| Oracle differential, random values (seed 20261026) | 3000 | 3000 |
| msgpack 1.2.3 differential (packb and unpackb) | 2000 | 2000 |
| Mutations of one nested value, settled by the oracle | 171 | 171 |
| Line protocol cases | 9 | 9 |

Named differences from the msgpack library: none. Its `packb` bytes matched the canonical bytes on every value it was given, and `unpackb` read the canonical bytes back to the same values.

Failures: none.
