/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MengerHamilton.Hamiltonian

/-!
# Degree-sequence conditions for Hamiltonian cycles: Chvátal and Pósa

For a finite simple graph `G` on `n ≥ 3` vertices with degree sequence `d₁ ≤ d₂ ≤ ⋯ ≤ dₙ`:

* `ChvatalPosa.chvatal`: **Chvátal (1972).** If for every `i < n/2`, `dᵢ ≤ i` implies
  `d_{n−i} ≥ n − i`, then `G` is Hamiltonian. Without sorting, `dᵢ ≤ i` says that at least `i`
  vertices have degree at most `i`, and `d_{n−i} ≥ n − i` says that at least `i + 1` vertices have
  degree at least `n − i`; the theorem is stated in this counting form.
* `ChvatalPosa.posa`: **Pósa (1962).** If for every `k` with `1 ≤ k < (n − 1)/2` fewer than `k`
  vertices have degree at most `k`, and, when `n` is odd, at most `(n − 1)/2` vertices have degree
  at most `(n − 1)/2`, then `G` is Hamiltonian.

Hamiltonicity is Mathlib's `SimpleGraph.IsHamiltonian`.
-/

@[expose] public section

open Finset SimpleGraph

namespace ChvatalPosa

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Chvátal's degree condition (counting form) for a graph `H`. -/
def ChvatalCond (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
    i ≤ #{v | H.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ H.degree v}

omit [DecidableEq V] in
/-- Chvátal's condition is preserved under adding edges. -/
lemma chvatalCond_mono {H H' : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (hle : H ≤ H') (h : ChvatalCond H) : ChvatalCond H' := by
  intro i hi hin hprem
  have hd : ∀ w, H.degree w ≤ H'.degree w := fun w => degree_le_of_le hle
  have h1 : i ≤ #{v | H.degree v ≤ i} := by
    refine hprem.trans (card_le_card ?_)
    intro w; simp only [mem_filter, mem_univ, true_and]; intro hw; exact (hd w).trans hw
  refine (h i hi hin h1).trans (card_le_card ?_)
  intro w; simp only [mem_filter, mem_univ, true_and]; intro hw; exact hw.trans (hd w)

omit [DecidableEq V] in
/-- If `S` contains every non-neighbour of `v` (including `v`), then `n ≤ deg v + #S`. -/
lemma card_le_degree_add_card (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V)
    (hS : ∀ w, ¬ H.Adj v w → w ∈ S) : Fintype.card V ≤ H.degree v + #S := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_univ]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w _
  by_cases hw : H.Adj v w
  · exact mem_union_left _ ((mem_neighborFinset _ _ _).2 hw)
  · exact mem_union_right _ (hS w hw)

omit [DecidableEq V] in
/-- Key step: under Chvátal's condition, a non-complete graph has two distinct non-adjacent
vertices whose degrees sum to at least `n`. -/
lemma exists_nonadj_degree_sum (H : SimpleGraph V) [DecidableRel H.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ChvatalCond H) (hnc : ∃ u v, u ≠ v ∧ ¬ H.Adj u v) :
    ∃ u v, u ≠ v ∧ ¬ H.Adj u v ∧ Fintype.card V ≤ H.degree u + H.degree v := by
  classical
  by_contra hcon
  push Not at hcon
  set n := Fintype.card V with hn_def
  obtain ⟨a, b, hab, hnab⟩ := hnc
  set P := (univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2) with hP
  have hPne : P.Nonempty := ⟨(a, b), by simp [hP, hab, hnab]⟩
  obtain ⟨p, hp, hmax⟩ := exists_max_image P (fun p => H.degree p.1 + H.degree p.2) hPne
  simp only [hP, mem_filter, mem_univ, true_and] at hp hmax
  have hmax' : ∀ x y, x ≠ y → ¬ H.Adj x y →
      H.degree x + H.degree y ≤ H.degree p.1 + H.degree p.2 :=
    fun x y hxy hn => hmax (x, y) ⟨hxy, hn⟩
  obtain ⟨u, v, huv, hnuv, hle, hmx⟩ : ∃ u v, u ≠ v ∧ ¬ H.Adj u v ∧ H.degree u ≤ H.degree v ∧
      ∀ x y, x ≠ y → ¬ H.Adj x y → H.degree x + H.degree y ≤ H.degree u + H.degree v := by
    rcases le_total (H.degree p.1) (H.degree p.2) with h12 | h21
    · exact ⟨p.1, p.2, hp.1, hp.2, h12, hmax'⟩
    · refine ⟨p.2, p.1, Ne.symm hp.1, fun h' => hp.2 (h'.symm), h21, ?_⟩
      intro x y hxy hn'; have := hmax' x y hxy hn'; omega
  have hsum := hcon u v huv hnuv
  set i := H.degree u with hi_def
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `u` is isolated: use the condition with `i = 1`.
    have hu1 : 1 ≤ #{w | H.degree w ≤ 1} :=
      card_pos.2 ⟨u, by simp only [mem_filter, mem_univ, true_and]; omega⟩
    have h2 : 1 + 1 ≤ #{w | n - 1 ≤ H.degree w} := h 1 le_rfl (by omega) hu1
    obtain ⟨w, hw, hwu⟩ := exists_mem_ne (by omega : 1 < #{w | n - 1 ≤ H.degree w}) u
    simp only [mem_filter, mem_univ, true_and] at hw
    by_cases hadj : H.Adj w u
    · have : 0 < H.degree u := by
        rw [← card_neighborFinset_eq_degree]
        exact card_pos.2 ⟨w, (mem_neighborFinset _ _ _).2 (hadj.symm)⟩
      omega
    · have hsub : H.neighborFinset w ⊆ (univ.erase w).erase u := by
        intro x hx
        rw [mem_neighborFinset] at hx
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, mem_univ _⟩⟩
        · rintro rfl; exact hadj hx
        · rintro rfl; exact hx.ne rfl
      have hc := card_le_card hsub
      rw [card_neighborFinset_eq_degree, card_erase_of_mem (mem_erase.2 ⟨hwu.symm, mem_univ _⟩),
        card_erase_of_mem (mem_univ _), card_univ] at hc
      omega
  · have h2i : 2 * i < n := by omega
    -- at least `i` vertices of degree `≤ i`
    have hA : i ≤ #{w | H.degree w ≤ i} := by
      have hS := card_le_degree_add_card H v (insert v ({w | H.degree w ≤ i} : Finset V)) (by
        intro w hw
        by_cases hwv : w = v
        · exact hwv ▸ mem_insert_self _ _
        · refine mem_insert_of_mem ?_
          simp only [mem_filter, mem_univ, true_and]
          have := hmx w v hwv (fun h' => hw (h'.symm))
          omega)
      have := card_insert_le v ({w | H.degree w ≤ i} : Finset V)
      omega
    have hB : i + 1 ≤ #{w | n - i ≤ H.degree w} := h i hipos h2i hA
    -- at least `n - i` vertices of degree `< n - i`
    have hT := card_le_degree_add_card H u {w | ¬ (n - i ≤ H.degree w)} (by
      intro w hw
      simp only [mem_filter, mem_univ, true_and]
      by_cases hwu : w = u
      · subst hwu; omega
      · have := hmx w u hwu (fun h' => hw (h'.symm))
        omega)
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun w => n - i ≤ H.degree w)
    rw [card_univ] at hsplit
    omega

/-- **Chvátal's theorem (1972), counting form.** A graph on `n ≥ 3` vertices is Hamiltonian if,
for every `i` with `1 ≤ i` and `2 i < n`, whenever at least `i` vertices have degree at most `i`,
at least `i + 1` vertices have degree at least `n - i`. -/
theorem chvatal (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian := by
  suffices key : ∀ N (H : SimpleGraph V) [DecidableRel H.Adj],
      #{p : V × V | p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2} = N → ChvatalCond H → H.IsHamiltonian from
    key _ G rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro H _ hN hH
  by_cases hall : ∀ u v, u ≠ v → H.Adj u v
  · exact Hamiltonicity.isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨u, v, huv, hnadj, hdeg⟩ := exists_nonadj_degree_sum H hn hH hall
  classical
  have hle : H ≤ H ⊔ edge u v := le_sup_left
  rw [← Hamiltonicity.isHamiltonian_sup_edge_iff H huv hnadj hdeg]
  refine ih _ ?_ (H ⊔ edge u v) rfl (chvatalCond_mono hle hH)
  rw [← hN]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(u, v), ?_, ?_⟩
    · simp [huv, hnadj]
    · simp [huv, edge_adj]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (hle h)⟩

/-- **Pósa's theorem (1962).** A graph on `n ≥ 3` vertices is Hamiltonian if, for every `k` with
`1 ≤ k` and `2 k < n - 1`, fewer than `k` vertices have degree at most `k`, and, when `n` is odd,
at most `(n - 1) / 2` vertices have degree at most `(n - 1) / 2`. -/
theorem posa (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian := by
  refine chvatal G hn fun i hi hin hprem => ?_
  set n := Fintype.card V
  by_cases hlt : 2 * i < n - 1
  · have := h₁ i hi hlt; omega
  · have hn' : n = 2 * i + 1 := by omega
    have hodd : Odd n := ⟨i, by omega⟩
    have hhalf : (n - 1) / 2 = i := by omega
    have hle := h₂ hodd
    rw [hhalf] at hle
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun w => G.degree w ≤ i)
    rw [card_univ] at hsplit
    have hsub : ({w | ¬ G.degree w ≤ i} : Finset V) ⊆ ({w | n - i ≤ G.degree w} : Finset V) := by
      intro w; simp only [mem_filter, mem_univ, true_and]; omega
    have := card_le_card hsub
    omega

end ChvatalPosa
