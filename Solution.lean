/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ChvatalPosaLib.ChvatalPosa

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `ChvatalPosaLib/ChvatalPosa.lean` (namespace `ChvatalPosa`) by the
Bondy–Chvátal closure argument, reusing `MengerHamilton/Hamiltonian.lean`
(`isHamiltonian_sup_edge_iff`: adding an edge `uv` with `deg u + deg v ≥ n` preserves
Hamiltonicity). Chvátal's condition is preserved under adding edges, and a non-complete graph
satisfying it has two non-adjacent vertices with degree sum at least `n`; adding such edges one
at a time reaches the complete graph. Pósa's condition implies Chvátal's.
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
    G.IsHamiltonian :=
  ChvatalPosa.chvatal G hn h

/-- **Pósa's theorem (1962).** A graph on `n ≥ 3` vertices is Hamiltonian if, for every `k` with
`1 ≤ k` and `2 k < n - 1`, fewer than `k` vertices have degree at most `k`, and, when `n` is odd,
at most `(n - 1) / 2` vertices have degree at most `(n - 1) / 2`. -/
theorem posa (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian :=
  ChvatalPosa.posa G hn h₁ h₂

end HamiltonDegree
