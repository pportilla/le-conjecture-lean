/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! # Finite smooth concatenation of paths with constant endpoint extensions

A finite sum of rescaled path increments gives one smooth path. Telescoping
proves its exact values on each stage and on every intervening constant interval.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace OnLeConjecture.Analytic

section Algebra
variable {E : Type*} [AddCommGroup E]

/-- The finite endpoint increments telescope. -/
theorem finitePath_sum_differences {N : ℕ} (C : Fin (N + 1) → E) :
    C 0 + ∑ j : Fin N, (C j.succ - C j.castSucc) = C (Fin.last N) := by
  have h := (Fin.sum_univ_succ C).symm.trans (Fin.sum_univ_castSucc C)
  rw [Finset.sum_sub_distrib]
  calc
    C 0 + ((∑ j : Fin N, C j.succ) - ∑ j : Fin N, C j.castSucc) =
        (C 0 + ∑ j : Fin N, C j.succ) - ∑ j : Fin N, C j.castSucc := by abel
    _ = ((∑ j : Fin N, C j.castSucc) + C (Fin.last N)) -
        ∑ j : Fin N, C j.castSucc := by rw [h]
    _ = C (Fin.last N) := by abel

/-- If only stage `j` is active, the sum of increments is that stage's value. -/
theorem finitePath_sum_eq_active {N : ℕ} (C : Fin (N + 1) → E) (v : Fin N → E)
    (j : Fin N) (hbefore : ∀ k, k < j → v k = C k.succ)
    (hafter : ∀ k, j < k → v k = C k.castSucc) :
    C 0 + ∑ k : Fin N, (v k - C k.castSucc) = v j := by
  let F : Fin (N + 1) → E := fun i => if i.val ≤ j.val then C i else v j
  have he (k : Fin N) : v k - C k.castSucc = F k.succ - F k.castSucc := by
    rcases lt_trichotomy k j with h | rfl | h
    · rw [hbefore k h]
      simp only [F, Fin.val_succ, Fin.val_castSucc,
        if_pos (show k.val + 1 ≤ j.val by omega), if_pos (show k.val ≤ j.val by omega)]
    · simp [F]
    · rw [hafter k h]
      simp only [F, Fin.val_succ, Fin.val_castSucc,
        if_neg (show ¬k.val + 1 ≤ j.val by omega), if_neg (show ¬k.val ≤ j.val by omega),
        sub_self]
  have h := finitePath_sum_differences F
  simpa only [← he, F, Fin.val_zero, Nat.zero_le, if_true, Fin.val_last,
    if_neg (show ¬N ≤ j.val from not_le.mpr j.isLt)] using h

/-- At a cut, all earlier stages have ended and all later stages have not begun. -/
theorem finitePath_sum_eq_cut {N : ℕ} (C : Fin (N + 1) → E) (v : Fin N → E)
    (i : Fin (N + 1)) (hbefore : ∀ k, k.val < i.val → v k = C k.succ)
    (hafter : ∀ k, i.val ≤ k.val → v k = C k.castSucc) :
    C 0 + ∑ k : Fin N, (v k - C k.castSucc) = C i := by
  let F : Fin (N + 1) → E := fun j => if j.val ≤ i.val then C j else C i
  have he (k : Fin N) : v k - C k.castSucc = F k.succ - F k.castSucc := by
    by_cases h : k.val < i.val
    · rw [hbefore k h]
      simp only [F, Fin.val_succ, Fin.val_castSucc,
        if_pos (show k.val + 1 ≤ i.val by omega), if_pos h.le]
    · rw [hafter k (by omega)]
      by_cases heq : k.val = i.val
      · have hc : k.castSucc = i := Fin.ext heq
        have hs : F k.succ = C i := by
          exact if_neg (show ¬k.succ.val ≤ i.val by simp only [Fin.val_succ]; omega)
        have hz : F k.castSucc = C i := by rw [hc]; simp [F]
        rw [hs, hz, hc, sub_self]
      · simp only [F, Fin.val_succ, Fin.val_castSucc,
          if_neg (show ¬k.val + 1 ≤ i.val by omega),
          if_neg (show ¬k.val ≤ i.val by omega), sub_self]
  have hf : F (Fin.last N) = C i := by
    by_cases h : i = Fin.last N
    · subst i; simp [F]
    · simp only [F, Fin.val_last, if_neg (show ¬N ≤ i.val by
        have hi := i.isLt
        have hne : i.val ≠ N := fun he => h (Fin.ext he)
        omega)]
  have h := finitePath_sum_differences F
  simpa only [← he, hf, F, Fin.val_zero, Nat.zero_le, if_true] using h

end Algebra

section Smooth
variable {E : Type*} [NormedAddCommGroup E]

/-- The finite sum of the rescaled path increments. -/
def finiteSmoothPathConcat {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ) (t : ℝ) : E :=
  C 0 + ∑ j : Fin N, (P j ((t - left j) / (right j - left j)) - C j.castSucc)

theorem finiteSmoothPathConcat_contDiff [NormedSpace ℝ E] {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hP : ∀ j, ContDiff ℝ ∞ (P j)) :
    ContDiff ℝ ∞ (finiteSmoothPathConcat C P left right) := by
  unfold finiteSmoothPathConcat
  apply contDiff_const.add
  apply ContDiff.sum
  intro j _
  exact ((hP j).comp ((contDiff_id.sub contDiff_const).div_const _)).sub contDiff_const

/-- Exact evaluation on a stage, including both endpoints. -/
theorem finiteSmoothPathConcat_stage {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (horder : ∀ j k, j < k → right j ≤ left k)
    (hstart : ∀ j t, t ≤ 0 → P j t = C j.castSucc)
    (hend : ∀ j t, 1 ≤ t → P j t = C j.succ)
    (j : Fin N) {t : ℝ} (ht : t ∈ Icc (left j) (right j)) :
    finiteSmoothPathConcat C P left right t = P j ((t - left j) / (right j - left j)) := by
  apply finitePath_sum_eq_active C _ j
  · intro k hkj
    apply hend
    apply (le_div_iff₀ (sub_pos.mpr (hlt k))).mpr
    have h := (horder k j hkj).trans ht.1
    linarith
  · intro k hjk
    apply hstart
    apply (div_le_iff₀ (sub_pos.mpr (hlt k))).mpr
    have h := ht.2.trans (horder j k hjk)
    linarith

/-- Exact value at any cut between completed and unstarted stages. -/
theorem finiteSmoothPathConcat_cut {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (hstart : ∀ j t, t ≤ 0 → P j t = C j.castSucc)
    (hend : ∀ j t, 1 ≤ t → P j t = C j.succ)
    (i : Fin (N + 1)) {t : ℝ}
    (hbefore : ∀ k, k.val < i.val → right k ≤ t)
    (hafter : ∀ k, i.val ≤ k.val → t ≤ left k) :
    finiteSmoothPathConcat C P left right t = C i := by
  apply finitePath_sum_eq_cut C _ i
  · intro k hki
    apply hend
    apply (le_div_iff₀ (sub_pos.mpr (hlt k))).mpr
    have h := hbefore k hki
    linarith
  · intro k hik
    apply hstart
    apply (div_le_iff₀ (sub_pos.mpr (hlt k))).mpr
    have h := hafter k hik
    linarith

@[simp] theorem finiteSmoothPathConcat_zero (C : Fin 1 → E)
    (P : Fin 0 → ℝ → E) (left right : Fin 0 → ℝ) (t : ℝ) :
    finiteSmoothPathConcat C P left right t = C 0 := by
  simp [finiteSmoothPathConcat]

/-- Before every stage starts, the concatenation is the initial value. -/
theorem finiteSmoothPathConcat_initial {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (hstart : ∀ j t, t ≤ 0 → P j t = C j.castSucc)
    {t : ℝ} (ht : ∀ j, t ≤ left j) :
    finiteSmoothPathConcat C P left right t = C 0 := by
  unfold finiteSmoothPathConcat
  have hz (j : Fin N) : P j ((t - left j) / (right j - left j)) - C j.castSucc = 0 := by
    rw [hstart j _ ((div_le_iff₀ (sub_pos.mpr (hlt j))).mpr (by have := ht j; linarith))]
    exact sub_self _
  simp only [hz, Finset.sum_const_zero, add_zero]

/-- After every stage ends, the concatenation is the final value. -/
theorem finiteSmoothPathConcat_final {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (hend : ∀ j t, 1 ≤ t → P j t = C j.succ)
    {t : ℝ} (ht : ∀ j, right j ≤ t) :
    finiteSmoothPathConcat C P left right t = C (Fin.last N) := by
  unfold finiteSmoothPathConcat
  have he (j : Fin N) : P j ((t - left j) / (right j - left j)) = C j.succ :=
    hend j _ ((le_div_iff₀ (sub_pos.mpr (hlt j))).mpr (by have := ht j; linarith))
  simp only [he]
  exact finitePath_sum_differences C

/-- Every gap between adjacent stages is constant at their common endpoint. -/
theorem finiteSmoothPathConcat_gap {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (horder : ∀ j k, j < k → right j ≤ left k)
    (hstart : ∀ j t, t ≤ 0 → P j t = C j.castSucc)
    (hend : ∀ j t, 1 ≤ t → P j t = C j.succ)
    (j k : Fin N) (hnext : k.val = j.val + 1) {t : ℝ}
    (ht : t ∈ Icc (right j) (left k)) :
    finiteSmoothPathConcat C P left right t = C j.succ := by
  apply finiteSmoothPathConcat_cut C P left right hlt hstart hend j.succ
  · intro q hq
    have hqj : q ≤ j := by simpa only [Fin.le_iff_val_le_val] using Nat.le_of_lt_succ hq
    rcases lt_or_eq_of_le hqj with h | rfl
    · exact (horder q j h).trans ((hlt j).le.trans ht.1)
    · exact ht.1
  · intro q hq
    have hkq : k ≤ q := by
      change k.val ≤ q.val
      simpa only [Fin.val_succ, hnext] using hq
    rcases lt_or_eq_of_le hkq with h | rfl
    · exact ht.2.trans ((hlt k).le.trans (horder k q h))
    · exact ht.2

omit [NormedAddCommGroup E] in
/-- A constant left extension and a collar at zero give a collar at every
nonpositive parameter. -/
theorem path_eventuallyEq_of_nonpos {P : ℝ → E} {A : E}
    (hplateau : ∀ t, t ≤ 0 → P t = A) (hcollar : P =ᶠ[𝓝 0] fun _ => A)
    {t : ℝ} (ht : t ≤ 0) : P =ᶠ[𝓝 t] fun _ => A := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · filter_upwards [continuousAt_id.eventually_lt continuousAt_const ht] with s hs
    exact hplateau s hs.le
  · exact hcollar

omit [NormedAddCommGroup E] in
/-- A constant right extension and a collar at one give a collar at every
parameter at least one. -/
theorem path_eventuallyEq_of_one_le {P : ℝ → E} {A : E}
    (hplateau : ∀ t, 1 ≤ t → P t = A) (hcollar : P =ᶠ[𝓝 1] fun _ => A)
    {t : ℝ} (ht : 1 ≤ t) : P =ᶠ[𝓝 t] fun _ => A := by
  rcases lt_or_eq_of_le ht with ht | heq
  · filter_upwards [continuousAt_const.eventually_lt continuousAt_id ht] with s hs
    exact hplateau s hs.le
  · subst t
    exact hcollar

/-- Endpoint collars on the stages produce a constant neighborhood at every
cut, even when two consecutive stage intervals touch. -/
theorem finiteSmoothPathConcat_cut_collar {N : ℕ} (C : Fin (N + 1) → E)
    (P : Fin N → ℝ → E) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j)
    (hstart : ∀ j t, t ≤ 0 → P j t = C j.castSucc)
    (hend : ∀ j t, 1 ≤ t → P j t = C j.succ)
    (hleft : ∀ j, P j =ᶠ[𝓝 0] fun _ => C j.castSucc)
    (hright : ∀ j, P j =ᶠ[𝓝 1] fun _ => C j.succ)
    (i : Fin (N + 1)) {t : ℝ}
    (hbefore : ∀ k, k.val < i.val → right k ≤ t)
    (hafter : ∀ k, i.val ≤ k.val → t ≤ left k) :
    finiteSmoothPathConcat C P left right =ᶠ[𝓝 t] fun _ => C i := by
  have hB (k : Fin N) : ∀ᶠ s in 𝓝 t,
      k.val < i.val → P k ((s - left k) / (right k - left k)) = C k.succ := by
    by_cases hki : k.val < i.val
    · have h := path_eventuallyEq_of_one_le
        (t := (t - left k) / (right k - left k)) (hend k) (hright k)
        ((le_div_iff₀ (sub_pos.mpr (hlt k))).mpr (by have := hbefore k hki; linarith))
      have hc : ContinuousAt (fun s : ℝ => (s - left k) / (right k - left k)) t := by fun_prop
      have he := h.comp_tendsto hc
      exact he.mono fun _ hs _ => hs
    · exact Filter.Eventually.of_forall fun _ h => (hki h).elim
  have hA (k : Fin N) : ∀ᶠ s in 𝓝 t,
      i.val ≤ k.val → P k ((s - left k) / (right k - left k)) = C k.castSucc := by
    by_cases hik : i.val ≤ k.val
    · have h := path_eventuallyEq_of_nonpos
        (t := (t - left k) / (right k - left k)) (hstart k) (hleft k)
        ((div_le_iff₀ (sub_pos.mpr (hlt k))).mpr (by have := hafter k hik; linarith))
      have hc : ContinuousAt (fun s : ℝ => (s - left k) / (right k - left k)) t := by fun_prop
      have he := h.comp_tendsto hc
      exact he.mono fun _ hs _ => hs
    · exact Filter.Eventually.of_forall fun _ h => (hik h).elim
  filter_upwards [Filter.eventually_all.mpr hB, Filter.eventually_all.mpr hA] with s hsB hsA
  exact finitePath_sum_eq_cut C _ i hsB hsA

end Smooth
end OnLeConjecture.Analytic
