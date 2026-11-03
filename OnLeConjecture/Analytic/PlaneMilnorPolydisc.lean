/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibre

/-!
# Polydisc fibres over a square base

For `H : Source 2 → ℂ`, write a point of `Source 2` as `z = (z 0, z 1)` and
call `z 0` the fibre coordinate and `z 1` the base coordinate. The square norm
of `x : ℂ` is `max |Re x| |Im x|`. The polydisc fibre with base radius `η`,
fibre radius `ρ` and level `s` is the actual set
`{z : squareNorm (z 1) ≤ η, ‖z 0‖ ≤ ρ, H z = s}`. The projection to the base
coordinate exhibits it as a branched covering of the closed square of radius `η`.
-/

@[expose] public noncomputable section

open Set Metric

namespace OnLeConjecture.Analytic

/-- The square norm `max |Re x| |Im x|` on `ℂ`. -/
def squareNorm (x : ℂ) : ℝ := max |x.re| |x.im|

/-- The closed square of radius `η` in `ℂ`. -/
def closedSquare (η : ℝ) : Set ℂ := {x | squareNorm x ≤ η}

/-- The polydisc fibre over the closed square of radius `η`, with fibre
radius `ρ` and level `s`. -/
def polydiscFibre (H : Source 2 → ℂ) (η ρ : ℝ) (s : ℂ) : Set (Source 2) :=
  {z | squareNorm (z 1) ≤ η ∧ ‖z 0‖ ≤ ρ ∧ H z = s}

/-- The derivative of `H` in the fibre direction `z 0`. -/
def fibrePartial (H : Source 2 → ℂ) (z : Source 2) : ℂ :=
  fderiv ℂ H z (Pi.single 0 1)

/-- The derivative of `H` in the base direction `z 1`. -/
def basePartial (H : Source 2 → ℂ) (z : Source 2) : ℂ :=
  fderiv ℂ H z (Pi.single 1 1)

theorem continuous_squareNorm : Continuous squareNorm := by
  unfold squareNorm
  fun_prop

theorem squareNorm_nonneg (x : ℂ) : 0 ≤ squareNorm x :=
  le_max_of_le_left (abs_nonneg _)

theorem squareNorm_le_norm (x : ℂ) : squareNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm x) (Complex.abs_im_le_norm x)

theorem norm_le_two_mul_squareNorm (x : ℂ) : ‖x‖ ≤ 2 * squareNorm x := by
  have h := Complex.norm_le_abs_re_add_abs_im x
  have h1 : |x.re| ≤ squareNorm x := le_max_left _ _
  have h2 : |x.im| ≤ squareNorm x := le_max_right _ _
  linarith

theorem squareNorm_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    squareNorm ((t : ℂ) * x) = t * squareNorm x := by
  simp only [squareNorm, Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul,
    abs_of_nonneg ht]
  exact (mul_max_of_nonneg _ _ ht).symm

theorem isClosed_closedSquare (η : ℝ) : IsClosed (closedSquare η) :=
  isClosed_le continuous_squareNorm continuous_const

theorem convex_closedSquare (η : ℝ) : Convex ℝ (closedSquare η) := by
  intro x hx y hy a b ha hb hab
  simp only [closedSquare, mem_ofPred_eq, squareNorm] at *
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul]
  refine max_le ?_ ?_
  · calc |a * x.re + b * y.re| ≤ a * |x.re| + b * |y.re| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * η + b * η := by
          gcongr
          · exact (le_max_left _ _).trans hx
          · exact (le_max_left _ _).trans hy
      _ = η := by rw [← add_mul, hab, one_mul]
  · calc |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * η + b * η := by
          gcongr
          · exact (le_max_right _ _).trans hx
          · exact (le_max_right _ _).trans hy
      _ = η := by rw [← add_mul, hab, one_mul]

theorem polydiscFibre_mono (H : Source 2 → ℂ) {η η' : ℝ} (h : η ≤ η') (ρ : ℝ) (s : ℂ) :
    polydiscFibre H η ρ s ⊆ polydiscFibre H η' ρ s :=
  fun _ hz => ⟨hz.1.trans h, hz.2.1, hz.2.2⟩

end OnLeConjecture.Analytic
