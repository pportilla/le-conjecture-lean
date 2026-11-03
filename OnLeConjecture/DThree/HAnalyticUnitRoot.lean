/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitRoot

/-!
# Analytic roots with a prescribed value

An analytic function which is nonzero at the origin admits an analytic root
of every positive order.  A chosen root of its value at the origin determines
the value of the analytic root.
-/

public section

namespace OnLeConjecture.DThree

/-- An analytic unit has an analytic `n`th root with any prescribed root of
its value at the origin. -/
theorem exists_analyticAt_root_with_value
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (c : ℂ) (hc : c ^ n = f 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧ g 0 = c ∧ ∀ z, g z ^ n = f z := by
  let normalized : ℂ → ℂ := fun z ↦ f z / f 0
  let g : ℂ → ℂ := fun z ↦
    c * normalized z ^ ((n : ℂ)⁻¹)
  have hnormalized : AnalyticAt ℂ normalized 0 := hf.div_const
  have hnormalizedZero : normalized 0 = 1 := by
    simp [normalized, hf0]
  have hg : AnalyticAt ℂ g 0 := by
    apply analyticAt_const.mul
    apply hnormalized.cpow analyticAt_const
    simpa only [hnormalizedZero] using Complex.one_mem_slitPlane
  refine ⟨g, hg, ?_, ?_⟩
  · simp [g, hnormalizedZero]
  · intro z
    rw [show g z = c * normalized z ^ ((n : ℂ)⁻¹) by rfl,
      mul_pow, Complex.cpow_nat_inv_pow _ hn, hc]
    exact mul_div_cancel₀ (f z) hf0

end OnLeConjecture.DThree

