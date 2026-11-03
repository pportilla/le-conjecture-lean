/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyModel
public import OnLeConjecture.Analytic.MultiSheetBraidFullTwist

/-!
# The local braid of an ordinary ramification point: the Coxeter word

At an ordinary ramification point of order `d` of the finite projection of Section 3 of the
written proof of Statement E, the `d` sheets of the cluster turn once counterclockwise by the
angle `2π / d`. This module proves that the explicit model of such a turn used in job J14, the
*cyclic shift* `cyclicShiftPath d` on `[0, 1]` (`MultiSheetBraidCyclicShift.lean`), is represented
through closed braids by the Coxeter word `σ_0 σ_1 ⋯ σ_{d-2}` (`isRepresented_cyclicShiftPath`).
During `[0, 1]` the point labelled `0` travels along the lower unit semicircle from `-1` to `1`,
and every other point moves counterclockwise along the upper semicircle to the position of its
neighbour.

The proof compares the cyclic shift, reparametrized so that it is performed during
`[0, (d - 1) / d]`, with the canonical closed braid of the Coxeter word by straight-line
interpolation, using the separation estimate `cyclicShift_separation` of job J14 on the first
`d - 1` letters of the full twist. Consequently every path word of the cyclic shift is conjugate
to the Coxeter word (`cyclicShiftPath_signedBraidConj`).
-/

@[expose] public noncomputable section

open Set Function Real

namespace OnLeConjecture.Analytic

open KnotTheory

variable {S : ℕ}

theorem fullTwistWord_eq_coxeter_append (S : ℕ) :
    fullTwistWord S = coxeterWord S ++ torusWord S (S - 1) := by
  rcases S with _ | n
  · rfl
  · simp [fullTwistWord, torusWord, List.replicate_succ]

theorem cyclicShiftPath_injective (hS : 2 ≤ S) (t : ℝ) :
    Injective fun k : Fin S => cyclicShiftPath S k t := by
  have h := angleFamily_injective hS (s := 1) ⟨zero_le_one, le_rfl⟩ (t / S)
  have hSr : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro k l hkl
  apply h
  simp only [angleFamily_one]
  rw [mul_div_cancel₀ t hSr]
  exact hkl

/-- The cyclic shift on `[0, 1]` is a closed braid with monodromy `(finRotate S)⁻¹`. -/
theorem cyclicShiftPath_isClosedStrandBraid (hS : 2 ≤ S) :
    IsClosedStrandBraid (cyclicShiftPath S) 0 1 (finRotate S)⁻¹ where
  lt := zero_lt_one
  continuousOn k := (cyclicShiftPath_continuous S k).continuousOn
  injective t _ := cyclicShiftPath_injective hS t
  closing k := by
    have := cyclicShiftPath_block hS (n := 1) (by omega) k
      (t := 0) ⟨le_rfl, zero_le_one⟩
    simpa [Equiv.Perm.inv_def] using this

/-- **The cyclic shift is represented by the Coxeter word.** -/
theorem isRepresented_cyclicShiftPath (hS : 2 ≤ S) :
    IsRepresentedByPositiveWord (cyclicShiftPath S) 0 1 (coxeterWord S) := by
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by linarith
  have hlen : ((coxeterWord S).length : ℝ) = (S : ℝ) - 1 := by
    rw [coxeterWord_length, Nat.cast_sub (by omega), Nat.cast_one]
  have hperm : (PositiveAdjacentWord.permutation (coxeterWord S))⁻¹ = (finRotate S)⁻¹ := by
    rw [← coxeterWord_permutation]
  have hK := cyclicShiftPath_isClosedStrandBraid hS
  -- The reparametrization performing the shift during `[0, (S - 1) / S]`.
  set ψ : ℝ → ℝ := fun t => min 1 ((S : ℝ) * t / ((S : ℝ) - 1)) with hψ
  have hψc : Continuous ψ := by fun_prop
  have hψm : MapsTo ψ (Icc 0 1) (Icc 0 1) := by
    intro t ht
    refine ⟨le_min zero_le_one (div_nonneg (by nlinarith [ht.1]) hS1.le), min_le_left _ _⟩
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hψ1 : ψ 1 = 1 := by
    simp only [hψ, mul_one]
    exact min_eq_left ((one_le_div hS1).mpr (by linarith))
  have h1 : ClosedStrandBraidIsotopic (fun k t => cyclicShiftPath S k (id t))
      (fun k t => cyclicShiftPath S k (ψ t)) 0 1 (finRotate S)⁻¹ :=
    ClosedStrandBraidIsotopic.of_reparam hK zero_lt_one continuous_id.continuousOn
      hψc.continuousOn (fun t ht => ht) hψm rfl rfl hψ0 hψ1
  -- The reparametrized shift is a closed braid.
  have hKψ : IsClosedStrandBraid (fun k t => cyclicShiftPath S k (ψ t)) 0 1 (finRotate S)⁻¹ :=
    h1.right
  have hM := positiveWordModel_isClosedStrandBraid (coxeterWord S) (zero_lt_one' ℝ)
  rw [hperm] at hM
  have h2 : ClosedStrandBraidIsotopic (fun k t => cyclicShiftPath S k (ψ t))
      (positiveWordModel (coxeterWord S) 0 1) 0 1 (finRotate S)⁻¹ := by
    refine ClosedStrandBraidIsotopic.of_separation hKψ hM fun t ht k l hkl => ?_
    -- The time of the canonical path.
    set τ := min ((S : ℝ) - 1) ((S : ℝ) * t) with hτ
    have hτmem : τ ∈ Icc (0 : ℝ) ((S : ℝ) * ((S : ℝ) - 1)) :=
      ⟨le_min hS1.le (by nlinarith [ht.1]), (min_le_left _ _).trans (by nlinarith)⟩
    have hsep := cyclicShift_separation hS hτmem hkl
    have hψτ : ψ t = τ / ((S : ℝ) - 1) := by
      simp only [hψ, hτ]
      rcases le_total ((S : ℝ) * t) ((S : ℝ) - 1) with h | h
      · rw [min_eq_right h, min_eq_right ((div_le_one hS1).mpr h)]
      · rw [min_eq_left h, div_self hS1.ne', min_eq_left ((one_le_div hS1).mpr h)]
    have hmodel : ∀ k : Fin S, positiveWordModel (coxeterWord S) 0 1 k t =
        positiveGridWord (fullTwistWord S) k τ := by
      intro k
      simp only [positiveWordModel, positiveWordModelTime, sub_zero, div_one, hlen]
      rw [fullTwistWord_eq_coxeter_append,
        positiveGridWord_append_of_le _ _ _ (by rw [hlen]; exact min_le_left _ _)]
      rcases le_total ((S : ℝ) * t) ((S : ℝ) - 1) with h | h
      · rw [show τ = (S : ℝ) * t from min_eq_right h]
        congr 1
        ring
      · rw [show τ = (S : ℝ) - 1 from min_eq_left h,
          positiveGridWord_of_length_le _ _ (by rw [hlen]; nlinarith [ht.2]),
          positiveGridWord_of_length_le _ _ (by rw [hlen])]
    rw [hψτ, hmodel, hmodel]
    exact hsep
  refine ⟨1, ?_⟩
  rw [hperm]
  simpa using h1.trans h2

/-- Every path word of the cyclic shift on `[0, 1]` is conjugate to the Coxeter word. -/
theorem cyclicShiftPath_signedBraidConj (hS : 2 ≤ S) {W : SignedAdjacentWord S}
    (hW : IsPathWord (cyclicShiftPath S) 0 1 W) :
    SignedBraidConj W (coxeterWord S).toSigned :=
  (isRepresented_cyclicShiftPath hS).signedBraidConj hW

end OnLeConjecture.Analytic
