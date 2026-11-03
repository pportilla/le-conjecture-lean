/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondGaps
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondDouble
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondAssembly

/-!
# Local identities for the second torus correction

This file collects the arithmetic identities and the evaluation lemmas used to
compute the coefficient formula at targets with five or six moved columns.

* `diag1` and `diag2` are the two diagonal identities `(M4A.2)` and `(M4A.4)` of
  the written proof. They express `T_p^0` through the four-point function `F`, the
  function `h_p` and the auxiliary functions `ψ₁`, `ψ₂` of `(M4A.6)`. The guarded
  forms `diag1_guard` and `diag2_guard` carry the adjacency condition as a
  conditional, so that a case analysis on the adjacency of two columns applies to
  them and to the coefficient formula simultaneously.
* `pentagon_identity` is the pentagon coefficient identity `(M6.12)`: the sum of
  the three-cycle and transposition coefficients over the five cyclic rotations of
  five points is the indicator of a balanced pentagon.
* `torusFourCoeff_cfgPerm_adj` evaluates the four-cycle coefficient of a
  transported permutation with the adjacency test on labels.
* `torusWeightSum_cfgPerm` and `weight_bound_of_sum` reduce the Alexander bound of
  a transported permutation to a linear inequality between its cyclic displacements.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- Decide every conditional settled by `omega`, split the first remaining one, and
recurse; close the leaves by introducing the hypotheses and calling `omega`. -/
syntax "prune_ifs'" : tactic
macro_rules
  | `(tactic| prune_ifs') =>
    `(tactic| (try simp (disch := omega) only [if_pos, if_neg]) <;>
      first | (intros; omega) | (split <;> prune_ifs'))

/-! ### The diagonal identities -/

/-- The function `ψ₁(s) = 1 + s + [s = p+1]` of `(M4A.6)`, modulo two. -/
def tcPsiOne (p s : ℕ) : ℕ := if s = p + 1 then s % 2 else (1 + s) % 2

/-- The function `ψ₂(s) = s + p [s = p]` of `(M4A.6)`, modulo two. -/
def tcPsiTwo (p s : ℕ) : ℕ := if s = p then 0 else s % 2

/-- The first diagonal identity `(M4A.2)`. -/
theorem diag1 (p A B : ℕ) (_hA : 2 ≤ A) (hAB : A < B) (hB : B ≤ 2 * p) :
    (tcT p A B + tcHp p A + tcHp p B + tcF p 1 A B) % 2 = tcPsiOne p A % 2 := by
  simp only [tcT, tcHp, tcF, tcPsiOne]
  prune_ifs

/-- The second diagonal identity `(M4A.4)`. -/
theorem diag2 (p r X Y : ℕ) (hr : 1 ≤ r) (hX : 2 ≤ X) (hXY : X < Y) (hY : r + Y = 2 * p + 1) :
    (tcT p X Y + tcF p r (r + 1) (r + X)) % 2 = tcPsiTwo p r % 2 := by
  simp only [tcT, tcF, tcPsiTwo]
  prune_ifs

/-- The first diagonal identity, guarded by the adjacency condition `g = 1`. -/
theorem diag1_guard (p g A B : ℕ) (hA : 2 ≤ A) (hAB : A < B) (hB : B ≤ 2 * p) :
    (if g = 1 then (tcT p A B + tcHp p A + tcHp p B + tcF p g A B) % 2 else 0) =
      (if g = 1 then tcPsiOne p A % 2 else 0) := by
  split_ifs with hg
  · subst hg; exact diag1 p A B hA hAB hB
  · rfl

/-- The second diagonal identity, guarded by the adjacency condition `g = 1`. -/
theorem diag2_guard (p g r s z X Y : ℕ) (hs : s = r + g) (hz : z = r + X) (hr : 1 ≤ r)
    (hX : 2 ≤ X) (hXY : X < Y) (hY : r + Y = 2 * p + 1) :
    (if g = 1 then (tcT p X Y + tcF p r s z) % 2 else 0) =
      (if g = 1 then tcPsiTwo p r % 2 else 0) := by
  split_ifs with hg
  · subst hg hs hz; exact diag2 p r X Y hr hX hXY hY
  · rfl

/-! ### The pentagon identity -/

/-- The pentagon coefficient identity `(M6.12)`, written through the five successive
gaps of five points in positive cyclic order. -/
theorem pentagon_identity (p g0 g1 g2 g3 g4 : ℕ) (h0 : 0 < g0) (h1 : 0 < g1) (h2 : 0 < g2)
    (h3 : 0 < g3) (h4 : 0 < g4) (hN : g0 + g1 + g2 + g3 + g4 = 2 * p + 1) :
    (tcF p g0 (g0 + g1) (g0 + g1 + g2) + tcF p g0 (g0 + g1) (g0 + g1 + g2 + g3) +
      (tcF p g1 (g1 + g2) (g1 + g2 + g3) + tcF p g1 (g1 + g2) (g1 + g2 + g3 + g4)) +
      (tcF p g2 (g2 + g3) (g2 + g3 + g4) + tcF p g2 (g2 + g3) (g2 + g3 + g4 + g0)) +
      (tcF p g3 (g3 + g4) (g3 + g4 + g0) + tcF p g3 (g3 + g4) (g3 + g4 + g0 + g1)) +
      (tcF p g4 (g4 + g0) (g4 + g0 + g1) + tcF p g4 (g4 + g0) (g4 + g0 + g1 + g2))) % 2 =
    if g0 + g1 ≤ p ∧ g1 + g2 ≤ p ∧ g2 + g3 ≤ p ∧ g3 + g4 ≤ p ∧ g4 + g0 ≤ p then 1 else 0 := by
  simp only [tcF]
  prune_ifs

/-! ### Adjacency on labels -/

theorem cycDist_fin_add_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) (i : Fin k) :
    cycDist i (i + 1) = 1 := by
  have h := cycDist_add_right i (1 : Fin k)
  rw [add_comm] at h
  rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]

/-- In a configuration in positive cyclic order, the only point at distance one after
`c i` can be `c (i + 1)`. -/
theorem exists_adj_iff {m k : ℕ} [NeZero k] (hk : 2 ≤ k) {c : Fin k ↪ Fin m}
    (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) (i : Fin k) :
    (∃ l, cycDist (c i) (c l) = 1 ∧ ρ l ≠ l) ↔
      cycDist (c i) (c (i + 1)) = 1 ∧ ρ (i + 1) ≠ i + 1 := by
  constructor
  · rintro ⟨l, hl, hρ⟩
    have hli : l ≠ i := by
      rintro rfl; rw [cycDist_self] at hl; exact absurd hl (by norm_num)
    have hle : cycDist (c i) (c (i + 1)) ≤ cycDist (c i) (c l) := by
      rw [cycDist_emb_le_iff hc, cycDist_fin_add_one hk]
      rw [Nat.one_le_iff_ne_zero, Ne, cycDist_eq_zero_iff]
      exact fun h => hli h.symm
    have hne : i ≠ i + 1 := by
      intro h
      have := cycDist_fin_add_one hk i
      rw [← h, cycDist_self] at this
      exact absurd this (by norm_num)
    have hpos : 0 < cycDist (c i) (c (i + 1)) := by
      rw [Nat.pos_iff_ne_zero, Ne, cycDist_eq_zero_iff, c.injective.eq_iff]
      exact hne
    have heq : cycDist (c i) (c (i + 1)) = cycDist (c i) (c l) := by omega
    have := c.injective (eq_of_cycDist_eq heq)
    rw [← this] at hl hρ
    exact ⟨hl, hρ⟩
  · rintro ⟨h1, h2⟩
    exact ⟨i + 1, h1, h2⟩

variable (n : ℕ)

/-- The four-cycle coefficient of a transported permutation, with the adjacency test
on labels. -/
theorem torusFourCoeff_cfgPerm_adj {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    {c : Fin k ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) :
    torusFourCoeff n (cfgPerm c ρ) =
      if ρ.support.card = 4 ∧ ∀ i, ρ (ρ i) = i → ρ i = i then
        ∑ i : Fin k, if ρ i ≠ i ∧ ρ (i + 1) ≠ i + 1 ∧ cycDist (c i) (c (i + 1)) = 1 then
          tcW4 (n + 1) (cycDist (c i) (c (ρ i))) (cycDist (c i) (c (ρ (ρ i))))
            (cycDist (c i) (c (ρ (ρ (ρ i)))))
        else 0
      else 0 := by
  rw [torusFourCoeff_cfgPerm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply propext
  rw [exists_adj_iff hk hc]
  tauto

/-! ### Pairs with a fixed column -/

/-- If the target moves neither three nor four columns, the pairs containing a fixed
column contribute nothing. -/
theorem sum_not_moved_eq_zero {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h0 : τ.support.card ≠ 0) (h3 : τ.support.card ≠ 3) (h4 : τ.support.card ≠ 4) (j : ℤ) :
    ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag.filter
        (fun p => ¬ (τ p.1 ≠ p.1 ∧ τ p.2 ≠ p.2)), pairTerm n τ j p.1 p.2 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter, Finset.mem_offDiag] at hp
  obtain ⟨⟨-, -, hne⟩, hm⟩ := hp
  by_cases h1 : τ p.1 = p.1
  · by_cases h2 : τ p.2 = p.2
    · exact pairTerm_of_fixed_fixed n τ j h1 h2 hne h0 h3
    · exact pairTerm_of_fixed_moved n τ j h1 h2 h3 h4
  · have h2 : τ p.2 = p.2 := by
      by_contra h2; exact hm ⟨h1, h2⟩
    exact pairTerm_of_moved_fixed n τ j h1 h2 h3 h4

/-- For a derangement of at least five labels, the coefficient formula is the sum over
the ordered pairs of distinct labels. -/
theorem coefFormula_cfgPerm_eq_sum {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (π : Equiv.Perm (Fin k)) (hπ : ∀ i, π i ≠ i) (hk : 5 ≤ k) (j : ℤ) :
    coefFormula n (cfgPerm c π) j =
      ∑ i : Fin k, ∑ l : Fin k, if i = l then 0 else
        pairTerm n (cfgPerm c π) j (c i) (c l) := by
  have hcard : (cfgPerm c π).support.card = k := by
    rw [card_support_cfgPerm]
    have : π.support = Finset.univ := by
      ext i; simp [Equiv.Perm.mem_support, hπ i]
    rw [this, Finset.card_univ, Fintype.card_fin]
  rw [coefFormula_cfgPerm_split n c π hπ j,
    sum_not_moved_eq_zero n (by omega) (by omega) (by omega), add_zero,
    sum_offDiag_eq_sum_sum (fun q => pairTerm n (cfgPerm c π) j (c q.1) (c q.2))]

/-! ### Displacement weights -/

/-- The scaled Alexander drop of a transported permutation is the sum of the weights of
the displacements of the configuration points. -/
theorem torusWeightSum_cfgPerm {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (ρ : Equiv.Perm (Fin k)) :
    torusWeightSum n (cfgPerm c ρ) =
      ∑ i : Fin k, reflectedTorusDisplacementWeight n (cycDist (c i) (c (ρ i))) := by
  unfold torusWeightSum
  rw [sum_eq_sum_emb c _ (fun x hx => by
    rw [cfgPerm_apply_of_notMem c ρ hx]
    simp [reflectedTorusCyclicDisplacement, reflectedTorusDisplacementWeight])]
  apply Finset.sum_congr rfl
  intro i _
  rw [cfgPerm_apply_emb]
  rfl

/-- If the displacements of a permutation wind `w` times around the grid, the
Alexander bound is the linear inequality `2p + Σ (d_i - (p+1)) ≤ p w`, where
`p = n + 1`. -/
theorem weight_bound_of_sum {k : ℕ} (d : Fin k → ℕ) (w : ℕ)
    (hsum : ∑ i, d i = w * consecutiveTorusGridSize n)
    (hcond : 2 * (n + 1) + ∑ i, (d i - (n + 2)) ≤ (n + 1) * w) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤
      ∑ i, reflectedTorusDisplacementWeight n (d i) := by
  unfold reflectedTorusDisplacementWeight
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : (∑ i, (d i : ℤ)) = (w : ℤ) * (consecutiveTorusGridSize n : ℤ) := by
    exact_mod_cast hsum
  have h2 : (2 * ((n : ℤ) + 1)) + ∑ i, ((d i - (n + 2) : ℕ) : ℤ) ≤ ((n : ℤ) + 1) * w := by
    exact_mod_cast hcond
  rw [h1]
  have hN : (0 : ℤ) ≤ consecutiveTorusGridSize n := Int.natCast_nonneg _
  nlinarith

/-- The Alexander bound for a transported permutation from the linear inequality of
its displacements. -/
theorem weight_bound_cfgPerm {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (ρ : Equiv.Perm (Fin k)) (w : ℕ)
    (hsum : ∑ i, cycDist (c i) (c (ρ i)) = w * consecutiveTorusGridSize n)
    (hcond : 2 * (n + 1) + ∑ i, (cycDist (c i) (c (ρ i)) - (n + 2)) ≤ (n + 1) * w) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n (cfgPerm c ρ) := by
  rw [torusWeightSum_cfgPerm]
  exact weight_bound_of_sum n (fun i => cycDist (c i) (c (ρ i))) w hsum hcond

end OnLeConjecture.KnotFloer.GridFull
