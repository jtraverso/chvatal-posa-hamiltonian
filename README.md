# Chvátal's and Pósa's degree conditions for Hamiltonian cycles in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Let `G` be a finite simple graph on `n ≥ 3` vertices with degree sequence `d₁ ≤ d₂ ≤ ⋯ ≤ dₙ`. All
statements are in the namespace `HamiltonDegree`; Hamiltonicity is Mathlib's
`SimpleGraph.IsHamiltonian`.

1. `chvatal`, **Chvátal's theorem (1972)**. If, for every `i < n/2`, `dᵢ ≤ i` implies
   `d_{n−i} ≥ n − i`, then `G` is Hamiltonian. The statement avoids sorting: "`dᵢ ≤ i`" is
   written as "at least `i` vertices have degree at most `i`", and "`d_{n−i} ≥ n − i`" as "at
   least `i + 1` vertices have degree at least `n − i`".
2. `posa`, **Pósa's theorem (1962)**. If, for every `k` with `1 ≤ k < (n − 1)/2`, fewer than `k`
   vertices have degree at most `k`, and, when `n` is odd, at most `(n − 1)/2` vertices have
   degree at most `(n − 1)/2`, then `G` is Hamiltonian.

Chvátal's condition contains the theorems of Dirac (1952), Ore (1960) and Pósa as special cases,
and is best possible among conditions on the degree sequence alone.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`ChvatalPosaLib/`](ChvatalPosaLib): the proofs.
- [`MengerHamilton/`](MengerHamilton): the Bondy–Chvátal closure lemma and related results,
  reused unchanged from the registered entry
  [PALOMAR-2026-10-15-000020](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000020&version=1)
  ([jtraverso/menger-hamiltonian](https://github.com/jtraverso/menger-hamiltonian) @ b6cf60e).
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Closure.** If `u` and `v` are non-adjacent and `deg u + deg v ≥ n`, then `G` is Hamiltonian
  if and only if `G + uv` is (Bondy–Chvátal; `isHamiltonian_sup_edge_iff` in `MengerHamilton`).
* **Chvátal.** The degree condition is preserved under adding edges. If `G` satisfies it and is
  not complete, a counting argument shows that some non-adjacent pair has degree sum at least
  `n`. Adding such edges one at a time reaches the complete graph, which is Hamiltonian for
  `n ≥ 3`.
* **Pósa.** Pósa's condition implies Chvátal's.

## Sources

* V. Chvátal, *On Hamilton's ideals*, J. Combin. Theory Ser. B 12 (1972) 163–168,
  doi:10.1016/0095-8956(72)90020-2.
* L. Pósa, *A theorem concerning Hamilton lines*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 7
  (1962) 225–226.
* J. A. Bondy, V. Chvátal, *A method in graph theory*, Discrete Math. 15 (1976) 111–135,
  doi:10.1016/0012-365X(76)90078-9 (the closure argument).

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
