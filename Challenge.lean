/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Degree-sequence conditions for Hamiltonian cycles: Chvátal and Pósa

For a finite simple graph `G` on `n ≥ 3` vertices with degree sequence `d₁ ≤ d₂ ≤ ⋯ ≤ dₙ`:

* `HamiltonDegree.chvatal`: **Chvátal (1972).** If for every `i < n/2`, `dᵢ ≤ i` implies
  `d_{n−i} ≥ n − i`, then `G` is Hamiltonian. Without sorting, `dᵢ ≤ i` says that at least `i`
  vertices have degree at most `i`, and `d_{n−i} ≥ n − i` says that at least `i + 1` vertices have
  degree at least `n − i`; the theorem is stated in this counting form.
* `HamiltonDegree.posa`: **Pósa (1962).** If for every `k` with `1 ≤ k < (n − 1)/2` fewer than `k`
  vertices have degree at most `k`, and, when `n` is odd, at most `(n − 1)/2` vertices have degree
  at most `(n − 1)/2`, then `G` is Hamiltonian.

Hamiltonicity is Mathlib's `SimpleGraph.IsHamiltonian`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace HamiltonDegree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Chvátal's theorem (1972), counting form.** A graph on `n ≥ 3` vertices is Hamiltonian if,
for every `i` with `1 ≤ i` and `2 i < n`, whenever at least `i` vertices have degree at most `i`,
at least `i + 1` vertices have degree at least `n - i`. -/
theorem chvatal (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian := by
  sorry

/-- **Pósa's theorem (1962).** A graph on `n ≥ 3` vertices is Hamiltonian if, for every `k` with
`1 ≤ k` and `2 k < n - 1`, fewer than `k` vertices have degree at most `k`, and, when `n` is odd,
at most `(n - 1) / 2` vertices have degree at most `(n - 1) / 2`. -/
theorem posa (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian := by
  sorry

end HamiltonDegree
