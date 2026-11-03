/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveFullTwistSheets

/-!
# Explicit transverse branch data and their common Puiseux parameter

This module treats the hypotheses of Theorem `J14:thm:factorization` of the written proof.
Branch `j` (`j < b`) is parametrized by `F_j(s) = (s^{a_j} v_j(s), s^{a_j})` with `a_j ≥ 1` and
`v_j` holomorphic on a disc. The factor `s^{a_j}` in the first coordinate is the order bound
`ord h_j ≥ a_j`, which is the transversality of the projection to the second coordinate
(Lemma `J14:lem:slope`). The parametrizations are jointly injective on the punctured disc:
two punctured parameters with the same image belong to the same branch and are equal.

With `q = ∏_j a_j` and `ω_a = e^{2πi/a}`, the strict-transform sheets of Lemma
`J14:lem:common` are `U_{jl}(t) = v_j(ω_{a_j}^l t^{q/a_j})`, `0 ≤ l < a_j`. They form sheet data
`MultiSheetData (∑_j a_j)` whose monodromy rotates the sheets of each branch cyclically. Its
number of cycles is `b`: two sheets lie in one cycle exactly when they belong to the same
branch, so the cycle of branch `j` consists of its `a_j` sheets. The root sheets are
`t^q U_{jl}(t) = h_j(s)` with `s = ω_{a_j}^l t^{q/a_j}` and `s^{a_j} = t^q`, that is, the first
coordinates of the points of the branch `j` over `ξ = t^q`.

Consequently (Corollary `J14:cor:cycles`) the positive words of
`MultiSheetData.exists_fullTwist_factorization` have exactly `b` permutation cycles.
-/

@[expose] public noncomputable section

open Set Filter Metric Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Explicit transverse branch data with `b` branches. -/
structure TransverseBranchData (b : ℕ) where
  /-- The degree of the projection of each branch to the second coordinate. -/
  a : Fin b → ℕ
  /-- The slope functions: branch `j` is `s ↦ (s^{a_j} v_j(s), s^{a_j})`. -/
  v : Fin b → ℂ → ℂ
  /-- The radius of the parameter discs. -/
  ρ : ℝ
  a_pos : ∀ j, 0 < a j
  ρ_pos : 0 < ρ
  analytic : ∀ j, AnalyticOnNhd ℂ (v j) (ball 0 ρ)
  separated : ∀ (j j' : Fin b) (s s' : ℂ), s ∈ ball (0 : ℂ) ρ → s' ∈ ball (0 : ℂ) ρ → s ≠ 0 →
    s ^ a j = s' ^ a j' → s ^ a j * v j s = s' ^ a j' * v j' s' → j = j' ∧ s = s'

namespace TransverseBranchData

variable {b : ℕ} (B : TransverseBranchData b)

/-- The number of strands, `∑_j a_j`. -/
def degree : ℕ := ∑ j, B.a j

/-- The common ramification index `∏_j a_j`. -/
def ramification : ℕ := ∏ j, B.a j

/-- The labelling of the sheets `(j, l)`, `l < a_j`, by `Fin (∑_j a_j)`. -/
def labels : (Σ j : Fin b, Fin (B.a j)) ≃ Fin B.degree := finSigmaFinEquiv

/-- The primitive root of unity `e^{2πi/n}`. -/
def unitRoot (n : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / n)

/-- The strict-transform sheet `(j, l)`. -/
def sheet (p : Σ j : Fin b, Fin (B.a j)) (t : ℂ) : ℂ :=
  B.v p.1 (unitRoot (B.a p.1) ^ p.2.val * t ^ (B.ramification / B.a p.1))

/-- The cyclic rotation of the sheets of every branch. -/
def rotation : Equiv.Perm (Σ j : Fin b, Fin (B.a j)) :=
  Equiv.sigmaCongrRight fun j => finRotate (B.a j)

theorem ramification_pos : 0 < B.ramification :=
  Finset.prod_pos fun j _ => B.a_pos j

theorem a_dvd_ramification (j : Fin b) : B.a j ∣ B.ramification :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

theorem unitRoot_pow_self {n : ℕ} (hn : 0 < n) : unitRoot n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one

theorem norm_unitRoot (n : ℕ) : ‖unitRoot n‖ = 1 := by
  unfold unitRoot
  rw [show 2 * (π : ℂ) * Complex.I / n = ((2 * π / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem unitRoot_pow_div {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    unitRoot (n * m) ^ m = unitRoot n := by
  unfold unitRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem quotient_pos (j : Fin b) : 0 < B.ramification / B.a j :=
  Nat.div_pos (Nat.le_of_dvd B.ramification_pos (B.a_dvd_ramification j)) (B.a_pos j)

theorem sheetParam_pow (j : Fin b) (l : ℕ) (t : ℂ) :
    (unitRoot (B.a j) ^ l * t ^ (B.ramification / B.a j)) ^ B.a j = t ^ B.ramification := by
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm l, pow_mul, unitRoot_pow_self (B.a_pos j),
    one_pow, one_mul, Nat.div_mul_cancel (B.a_dvd_ramification j)]

theorem sheet_mem_ball {p : Σ j : Fin b, Fin (B.a j)} {t : ℂ} (ht : t ∈ ball (0 : ℂ) (min B.ρ 1)) :
    unitRoot (B.a p.1) ^ p.2.val * t ^ (B.ramification / B.a p.1) ∈ ball (0 : ℂ) B.ρ := by
  have ht1 : ‖t‖ < 1 := lt_of_lt_of_le (mem_ball_zero_iff.mp ht) (min_le_right _ _)
  have htρ : ‖t‖ < B.ρ := lt_of_lt_of_le (mem_ball_zero_iff.mp ht) (min_le_left _ _)
  rw [mem_ball_zero_iff, norm_mul, norm_pow, norm_unitRoot, one_pow, one_mul, norm_pow]
  have hm := B.quotient_pos p.1
  calc ‖t‖ ^ (B.ramification / B.a p.1) ≤ ‖t‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) ht1.le hm
    _ = ‖t‖ := pow_one _
    _ < B.ρ := htρ

theorem sheet_analytic (p : Σ j : Fin b, Fin (B.a j)) :
    AnalyticOnNhd ℂ (B.sheet p) (ball 0 (min B.ρ 1)) := by
  intro t ht
  change AnalyticAt ℂ (fun t => B.v p.1 (unitRoot (B.a p.1) ^ p.2.val *
    t ^ (B.ramification / B.a p.1))) t
  exact (B.analytic p.1 _ (B.sheet_mem_ball ht)).comp
    (f := fun t => unitRoot (B.a p.1) ^ p.2.val * t ^ (B.ramification / B.a p.1)) (by fun_prop)

/-- Rotating the source parameter by `e^{2πi/q}` rotates the sheets of each branch. -/
theorem sheet_monodromy (p : Σ j : Fin b, Fin (B.a j)) (t : ℂ) :
    B.sheet p (unitRoot B.ramification * t) = B.sheet (B.rotation p) t := by
  obtain ⟨j, l⟩ := p
  have haj := B.a_pos j
  set m := B.ramification / B.a j with hmdef
  have hm : 0 < m := B.quotient_pos j
  have hq : B.ramification = B.a j * m :=
    (Nat.mul_div_cancel' (B.a_dvd_ramification j)).symm
  have hroot : unitRoot B.ramification ^ m = unitRoot (B.a j) := by
    calc unitRoot B.ramification ^ m = unitRoot (B.a j * m) ^ m := by rw [← hq]
      _ = unitRoot (B.a j) := unitRoot_pow_div haj hm
  have hval : ((finRotate (B.a j)) l).val = (l.val + 1) % B.a j := by
    have := finRotate_pow_apply_val (S := B.a j) 1 l
    simpa using this
  change B.v j (unitRoot (B.a j) ^ l.val * (unitRoot B.ramification * t) ^ m) =
    B.v j (unitRoot (B.a j) ^ ((finRotate (B.a j)) l).val * t ^ m)
  congr 1
  rw [mul_pow, ← mul_assoc, hroot, ← pow_succ, hval]
  congr 1
  conv_lhs => rw [← Nat.mod_add_div (l.val + 1) (B.a j)]
  rw [pow_add, pow_mul, unitRoot_pow_self haj, one_pow, mul_one]

/-- Two distinct sheets have distinct germs. -/
theorem sheet_distinct {p p' : Σ j : Fin b, Fin (B.a j)} (hpp : p ≠ p') :
    ¬ (B.sheet p =ᶠ[𝓝 0] B.sheet p') := by
  intro h
  obtain ⟨j, l⟩ := p
  obtain ⟨j', l'⟩ := p'
  have hm := B.quotient_pos j
  have hm' := B.quotient_pos j'
  have hq : B.ramification = B.a j * (B.ramification / B.a j) :=
    (Nat.mul_div_cancel' (B.a_dvd_ramification j)).symm
  have hq' : B.ramification = B.a j' * (B.ramification / B.a j') :=
    (Nat.mul_div_cancel' (B.a_dvd_ramification j')).symm
  have hball : ball (0 : ℂ) (min B.ρ 1) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ (lt_min B.ρ_pos one_pos)
  obtain ⟨t, ⟨⟨htE, htB⟩, ht0⟩⟩ :=
    ((h.and (Filter.eventually_of_mem hball fun _ h => h)).filter_mono
    nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℂ))
  change t ≠ 0 at ht0
  set s := unitRoot (B.a j) ^ l.val * t ^ (B.ramification / B.a j)
  set s' := unitRoot (B.a j') ^ l'.val * t ^ (B.ramification / B.a j')
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ (by
    unfold unitRoot; exact Complex.exp_ne_zero _)) (pow_ne_zero _ ht0)
  have hspow : s ^ B.a j = t ^ B.ramification := B.sheetParam_pow j l.val t
  have hspow' : s' ^ B.a j' = t ^ B.ramification := B.sheetParam_pow j' l'.val t
  have hsheet : B.v j s = B.v j' s' := htE
  obtain ⟨hjj, hss⟩ := B.separated j j' s s' (B.sheet_mem_ball (p := ⟨j, l⟩) htB)
    (B.sheet_mem_ball (p := ⟨j', l'⟩) htB) hs0 (hspow.trans hspow'.symm)
    (by rw [hspow, hspow', hsheet])
  subst hjj
  apply hpp
  have hroots : unitRoot (B.a j) ^ l.val = unitRoot (B.a j) ^ l'.val :=
    mul_right_cancel₀ (pow_ne_zero _ ht0) hss
  have hinj := (Complex.isPrimitiveRoot_exp (B.a j) (B.a_pos j).ne').pow_inj l.isLt l'.isLt hroots
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hinj))

/-- The sheet data of the branches, for a labelling `e` of the sheets by `Fin S`. -/
def toMultiSheetData {S : ℕ} (e : (Σ j : Fin b, Fin (B.a j)) ≃ Fin S) : MultiSheetData S where
  q := B.ramification
  U k := B.sheet (e.symm k)
  R := min B.ρ 1
  τ := e.symm.trans (B.rotation.trans e)
  q_pos := B.ramification_pos
  R_pos := lt_min B.ρ_pos one_pos
  analytic k := B.sheet_analytic _
  distinct k l hkl := B.sheet_distinct (fun h => hkl (e.symm.injective h))
  monodromy k t _ := by
    change B.sheet _ (unitRoot B.ramification * t) = _
    rw [B.sheet_monodromy]
    simp

/-- The root sheets are the first coordinates of the branch points over `ξ = t^q`: the
root sheet labelled `k` is `s^{a_j} v_j(s)` for the parameter
`s = ω_{a_j}^l t^{q/a_j}` of branch `j`, where `(j, l)` is the branch label of `k`, and
`s^{a_j} = t^q`. -/
theorem rootSheet_eq {S : ℕ} (e : (Σ j : Fin b, Fin (B.a j)) ≃ Fin S) (k : Fin S) (t : ℂ) :
    (B.toMultiSheetData e).rootSheet k t =
      (unitRoot (B.a (e.symm k).1) ^ (e.symm k).2.val *
          t ^ (B.ramification / B.a (e.symm k).1)) ^ B.a (e.symm k).1 *
        B.v (e.symm k).1 (unitRoot (B.a (e.symm k).1) ^ (e.symm k).2.val *
          t ^ (B.ramification / B.a (e.symm k).1)) ∧
      (unitRoot (B.a (e.symm k).1) ^ (e.symm k).2.val *
          t ^ (B.ramification / B.a (e.symm k).1)) ^ B.a (e.symm k).1 =
        t ^ B.ramification := by
  have hpow := B.sheetParam_pow (e.symm k).1 (e.symm k).2.val t
  refine ⟨?_, hpow⟩
  rw [hpow]
  rfl

/-- Two sheets lie in the same cycle of the monodromy if and only if they belong to the same
branch. In particular the cycle of the sheets of branch `j` consists of its `a_j` sheets. -/
theorem sameCycle_monodromy_iff {S : ℕ} (e : (Σ j : Fin b, Fin (B.a j)) ≃ Fin S)
    (k k' : Fin S) :
    (B.toMultiSheetData e).τ.SameCycle k k' ↔ (e.symm k).1 = (e.symm k').1 := by
  classical
  have hA : ∀ (n : ℕ) (p : Σ j : Fin b, Fin (B.a j)),
      (B.rotation ^ n) p = ⟨p.1, ((finRotate (B.a p.1)) ^ n) p.2⟩ := by
    intro n
    induction n with
    | zero => intro p; rfl
    | succ n ih =>
      intro p
      rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
      rfl
  have hB : ∀ (n : ℕ) (k : Fin S),
      ((B.toMultiSheetData e).τ ^ n) k = e ((B.rotation ^ n) (e.symm k)) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
      change e (B.rotation (e.symm (e _))) = _
      rw [Equiv.symm_apply_apply]
  have hsame : ∀ p p' : Σ j : Fin b, Fin (B.a j), p.1 = p'.1 →
      ∃ n : ℕ, (B.rotation ^ n) p = p' := by
    rintro ⟨j, l⟩ ⟨j', l'⟩ hj
    simp only at hj
    subst hj
    obtain ⟨n, hn⟩ := (planeBranchBraidLabel_sameCycle (B.a_pos j) l l').exists_nat_pow_eq
    exact ⟨n, by rw [hA, hn]⟩
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hB, ← Equiv.eq_symm_apply, hA] at hn
    rw [← hn]
  · intro h
    obtain ⟨n, hn⟩ := hsame _ _ h
    refine ⟨n, ?_⟩
    rw [zpow_natCast, hB, hn, Equiv.apply_symm_apply]

/-- The monodromy has exactly `b` cycles, one for each branch
(Corollary `J14:cor:cycles`). -/
theorem permCycleCount_monodromy {S : ℕ} (e : (Σ j : Fin b, Fin (B.a j)) ≃ Fin S) :
    permCycleCount (B.toMultiSheetData e).τ = b := by
  classical
  have hτ := B.sameCycle_monodromy_iff e
  unfold permCycleCount
  let f : Quotient (Equiv.Perm.SameCycle.setoid (B.toMultiSheetData e).τ) → Fin b :=
    Quotient.lift (fun k => (e.symm k).1) fun k k' h => (hτ k k').mp h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      exact Quotient.sound ((hτ _ _).mpr hxy)
    · intro j
      exact ⟨Quotient.mk _ (e ⟨j, ⟨0, B.a_pos j⟩⟩), by simp [f]⟩
  rw [Fintype.card_of_bijective hf, Fintype.card_fin]

end TransverseBranchData

end OnLeConjecture.Analytic
