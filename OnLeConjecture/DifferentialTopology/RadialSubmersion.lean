/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A curve criterion for a joint submersion

If one differential is surjective and a curve in its kernel changes a
second real-valued function with nonzero derivative, their product
differential is surjective. This will be applied to a plane equation and
the squared ambient norm.
-/

public noncomputable section

open Filter Function
open scoped Topology

namespace OnLeConjecture.DifferentialTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real linear functional nonzero on the kernel supplies the missing
coordinate of a product map. -/
theorem surjective_prod_of_surjective_of_nonzero_on_ker
    (f : E →L[ℝ] F) (g : E →L[ℝ] ℝ) (hf : Surjective f)
    (v : E) (hv : f v = 0) (hgv : g v ≠ 0) :
    Surjective (f.prod g) := by
  rintro ⟨a, b⟩
  obtain ⟨w, hw⟩ := hf a
  refine ⟨w + ((b - g w) / g v) • v, ?_⟩
  apply Prod.ext
  · change f (w + ((b - g w) / g v) • v) = a
    simp only [map_add, map_smul, hv, smul_zero,
      add_zero, hw]
  · change g (w + ((b - g w) / g v) • v) = b
    simp only [map_add, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hgv]
    exact add_sub_cancel _ _

/-- A differentiable curve in a level set, whose second function is the
curve parameter, proves surjectivity of the joint differential. -/
theorem surjective_fderiv_pair_of_level_curve
    {f : E → F} {g : E → ℝ} {x : E} {c : ℝ} {q : ℝ → E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hs : Surjective (fderiv ℝ f x))
    (hq : DifferentiableAt ℝ q c) (hqc : q c = x)
    (hfq : (fun t => f (q t)) =ᶠ[𝓝 c] fun _ => f x)
    (hgq : (fun t => g (q t)) =ᶠ[𝓝 c] id) :
    Surjective (fderiv ℝ (fun y => (f y, g y)) x) := by
  have hf' : DifferentiableAt ℝ f (q c) := hqc.symm ▸ hf
  have hg' : DifferentiableAt ℝ g (q c) := hqc.symm ▸ hg
  have hdf : fderiv ℝ f x (fderiv ℝ q c 1) = 0 := by
    have he := congrArg (fun L : ℝ →L[ℝ] F => L 1) (hfq.fderiv_eq (𝕜 := ℝ))
    change (fderiv ℝ (f ∘ q) c) 1 = (fderiv ℝ (fun _ : ℝ => f x) c) 1 at he
    rw [fderiv_comp c hf' hq, fderiv_const_apply] at he
    simpa only [ContinuousLinearMap.comp_apply, hqc, zero_apply] using he
  have hdg : fderiv ℝ g x (fderiv ℝ q c 1) = 1 := by
    have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hgq.fderiv_eq (𝕜 := ℝ))
    change (fderiv ℝ (g ∘ q) c) 1 = (fderiv ℝ id c) 1 at he
    rw [fderiv_comp c hg' hq] at he
    simpa only [ContinuousLinearMap.comp_apply, hqc,
      fderiv_id, ContinuousLinearMap.id_apply] using he
  rw [(hf.hasFDerivAt.prodMk hg.hasFDerivAt).fderiv]
  exact surjective_prod_of_surjective_of_nonzero_on_ker _ _ hs
    (fderiv ℝ q c 1) hdf (by rw [hdg]; exact one_ne_zero)

end OnLeConjecture.DifferentialTopology
