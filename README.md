# Rectilinear planarity of SP-graphs: Lean 4 formalization

Lean 4 (v4.35.0) + Mathlib (v4.35.0) formalization accompanying the paper on
rectilinear planarity testing of biconnected series-parallel graphs with maximum
degree 4 and k degree-4 vertices in 2^{O(k)}·n time.

All theorems depend only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound` (no `sorry`), as reported by the `#print axioms` commands in the file.

## Build

```
lake exe cache get
lake build
```

## Main results

| Paper | Lean name |
|---|---|
| Key Lemma | `KeyLemma.key_lemma` |
| Symmetry of spirality sets | `RectilinearSP.T1_1` |
| Light trees: parity and interval shape | `T1_2`, `T1_3` |
| Finiteness | `T2_0` |
| Light P-node does not increase pieces | `T2_1` |
| Pieces under S, P2, P3 nodes | `T3_1`–`T3_4` |
| pieces ≤ 36^{costly} | `T4_3` |
| costly ≤ 2·heavyP, pieces ≤ 36^{2·heavyP} | `T5_1`, `T5_2` |
| Algorithm correctness and output size | `T6a_1`–`T6a_3` |
| Endpoint normalization | `normalizeE_eq`, `T6a'_1`, `T6a'_2` |
| Endpoint algorithm = reference algorithm | `T6a'_3`, `T6a'_4` |
| Total cost (fixed root) | `T6b` |
| Root test and its cost | `T6d_1`, `T6d_2` |

Not formalized (on paper or cited): the DKLO rules used as definitions,
heavyP ≤ 2k, and the reusability principle (Lemma 5.11 of arXiv:2502.03309).
