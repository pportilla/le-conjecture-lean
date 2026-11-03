/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondTriangleSplit

/-!
# Configurations with inserted columns

This file builds configurations from explicit lists of columns in positive cyclic
order (`mkCfg`), compares transported permutations along two configurations
(`cfgPerm_eq_of_compat`), and evaluates the four-cycle and the three-cycle and
transposition coefficients of configurations of four and five columns through their
successive gaps (`four_eval`, `five_eval`).
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

section Construction

variable {m k : ℕ} [NeZero k]

/-- The configuration given by columns in positive cyclic order. -/
def mkCfg (f : Fin k → Fin m) (hf : StrictMono fun i => cycDist (f 0) (f i)) : Fin k ↪ Fin m :=
  ⟨f, fun i j h => hf.injective (by simp only [h])⟩

@[simp] theorem mkCfg_apply (f : Fin k → Fin m) (hf : StrictMono fun i => cycDist (f 0) (f i))
    (i : Fin k) : mkCfg f hf i = f i := rfl

theorem cycSorted_mkCfg (f : Fin k → Fin m) (hf : StrictMono fun i => cycDist (f 0) (f i)) :
    CycSorted (mkCfg f hf) := hf

end Construction

/-- Two transported permutations agree when the labels of one configuration embed in the
labels of the other compatibly with the patterns, and the other labels are fixed. -/
theorem cfgPerm_eq_of_compat {m k k' : ℕ} (c : Fin k ↪ Fin m) (d : Fin k' ↪ Fin m)
    (ρ : Equiv.Perm (Fin k)) (ρ' : Equiv.Perm (Fin k')) (ι : Fin k → Fin k')
    (hι : ∀ i, d (ι i) = c i) (hρ : ∀ i, ρ' (ι i) = ι (ρ i))
    (hfix : ∀ l, (∀ i, ι i ≠ l) → ρ' l = l) : cfgPerm c ρ = cfgPerm d ρ' := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range d
  · obtain ⟨l, rfl⟩ := hx
    by_cases hl : ∃ i, ι i = l
    · obtain ⟨i, rfl⟩ := hl
      have h1 : cfgPerm d ρ' (d (ι i)) = c (ρ i) := by rw [cfgPerm_apply_emb, hρ, hι]
      have h2 : cfgPerm c ρ (d (ι i)) = c (ρ i) := by rw [hι, cfgPerm_apply_emb]
      rw [h1, h2]
    · simp only [not_exists] at hl
      rw [cfgPerm_apply_emb, hfix l hl]
      apply cfgPerm_apply_of_notMem
      rintro ⟨i, hi⟩
      rw [← hι] at hi
      exact hl i (d.injective hi)
  · rw [cfgPerm_apply_of_notMem d ρ' hx]
    apply cfgPerm_apply_of_notMem
    rintro ⟨i, rfl⟩
    exact hx ⟨ι i, hι i⟩

/-! ### Distances as sums of gaps -/

/-- The sum of the gaps `g s` over the labels `s` of the half-open interval `[i, l)`. -/
def gapSum {k : ℕ} (g : Fin k → ℕ) (i l : Fin k) : ℕ := ∑ s, if IdxIco i l s then g s else 0

set_option maxRecDepth 10000 in
theorem cycDist_eq_gapSum_four {m : ℕ} {c : Fin 4 ↪ Fin m} (hc : CycSorted c) (i l : Fin 4) :
    cycDist (c i) (c l) = gapSum (fun s => cycDist (c s) (c (s + 1))) i l := by
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, -, -⟩ := cycDist_gaps_4 hc
  fin_cases i <;> fin_cases l <;>
    simp (config := {decide := true}) only [gapSum, Fin.sum_univ_four, Fin.isValue,
      Fin.reduceAdd, ite_true, ite_false, add_zero, zero_add, cycDist_self, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk] <;> omega

set_option maxRecDepth 10000 in
theorem cycDist_eq_gapSum_five {m : ℕ} {c : Fin 5 ↪ Fin m} (hc : CycSorted c) (i l : Fin 5) :
    cycDist (c i) (c l) = gapSum (fun s => cycDist (c s) (c (s + 1))) i l := by
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩, -, -⟩ :=
    cycDist_gaps_5 hc
  fin_cases i <;> fin_cases l <;>
    simp (config := {decide := true}) only [gapSum, Fin.sum_univ_five, Fin.isValue,
      Fin.reduceAdd, ite_true, ite_false, add_zero, zero_add, cycDist_self, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk] <;> omega

/-! ### Coefficients through gaps -/

/-- The four-cycle coefficient of a pattern on four labels with successive gaps `g`. -/
def fourGap (p : ℕ) (π : Equiv.Perm (Fin 4)) (g : Fin 4 → ℕ) : ℕ :=
  if π.support.card = 4 ∧ ∀ i, π (π i) = i → π i = i then
    ∑ i : Fin 4, if π i ≠ i ∧ π (i + 1) ≠ i + 1 ∧ g i = 1 then
      tcW4 p (gapSum g i (π i)) (gapSum g i (π (π i))) (gapSum g i (π (π (π i))))
    else 0
  else 0

/-- The three-cycle and transposition coefficient of a pattern on five labels with
successive gaps `g`. -/
def fiveGap (p : ℕ) (π : Equiv.Perm (Fin 5)) (g : Fin 5 → ℕ) : ℕ :=
  if π.support.card = 5 then
    ∑ i : Fin 5, ∑ l : Fin 5, if FiveCondIdx π i l then
      tcF p (gapSum g i l) (gapSum g i (π i)) (gapSum g i (π l)) +
        tcF p (gapSum g i l) (gapSum g i (π i)) (gapSum g i (π (π l)))
    else 0
  else 0

variable (n : ℕ)

theorem four_eval {c : Fin 4 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c)
    (π : Equiv.Perm (Fin 4)) :
    torusFourCoeff n (cfgPerm c π) = fourGap (n + 1) π (fun s => cycDist (c s) (c (s + 1))) := by
  rw [torusFourCoeff_cfgPerm_adj n (by norm_num) hc, fourGap]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cycDist_eq_gapSum_four hc i (π i), cycDist_eq_gapSum_four hc i (π (π i)),
    cycDist_eq_gapSum_four hc i (π (π (π i)))]

theorem five_eval {c : Fin 5 ↪ Fin (consecutiveTorusGridSize n)} (hc : CycSorted c)
    (π : Equiv.Perm (Fin 5)) :
    torusFiveCoeff n (cfgPerm c π) = fiveGap (n + 1) π (fun s => cycDist (c s) (c (s + 1))) := by
  rw [torusFiveCoeff_cfgPerm n hc, fiveGap]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [cycDist_eq_gapSum_five hc i l, cycDist_eq_gapSum_five hc i (π i),
    cycDist_eq_gapSum_five hc i (π l), cycDist_eq_gapSum_five hc i (π (π l))]

end OnLeConjecture.KnotFloer.GridFull
