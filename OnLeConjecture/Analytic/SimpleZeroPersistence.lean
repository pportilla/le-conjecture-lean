/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Complex.Basic

/-!
# Persistence of a simple zero

This file applies the implicit function theorem to a complex parameter and a
Banach space of point variables.  A zero persists along a local branch when
the joint map is strictly differentiable and its derivative in the point
variables is invertible.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The branch supplied by the implicit function theorem for a simple zero. -/
@[expose]
noncomputable def simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    ℂ → E :=
  hPhi.implicitFunctionOfProdDomain hpoint

/-- The implicit branch passes through the prescribed zero. -/
@[simp]
theorem simpleZeroBranch_apply_zero
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    simpleZeroBranch Phi p Phi' hPhi hpoint 0 = p := by
  have hbase :=
    (hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint).self_of_nhds
  simpa [simpleZeroBranch] using hbase.mp rfl

/-- The implicit branch converges to the prescribed zero as the parameter
converges to zero. -/
theorem tendsto_simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    Tendsto (simpleZeroBranch Phi p Phi' hPhi hpoint) (nhds 0) (nhds p) := by
  simpa [simpleZeroBranch] using
    hPhi.tendsto_implicitFunctionOfProdDomain hpoint

/-- The implicit branch consists of zeros near the base parameter. -/
theorem eventually_simpleZeroBranch_eq_zero
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hzero : Phi (0, p) = 0)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    ∀ᶠ lambda in nhds 0,
      Phi (lambda, simpleZeroBranch Phi p Phi' hPhi hpoint lambda) = 0 := by
  simpa [simpleZeroBranch, hzero] using
    hPhi.eventually_apply_implicitFunctionOfProdDomain hpoint

/-- The derivative of the implicit branch at the base parameter. -/
theorem hasStrictFDerivAt_simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    HasStrictFDerivAt (simpleZeroBranch Phi p Phi' hPhi hpoint)
      (-((Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).inverse) ∘L
        (Phi' ∘L ContinuousLinearMap.inl ℂ ℂ E)) 0 := by
  simpa [simpleZeroBranch] using
    hPhi.hasStrictFDerivAt_implicitFunctionOfProdDomain hpoint

/-- Existence of a local zero branch from an invertible point derivative. -/
theorem exists_simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hzero : Phi (0, p) = 0)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    ∃ branch : ℂ → E,
      branch 0 = p ∧
      Tendsto branch (nhds 0) (nhds p) ∧
      ∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0 := by
  refine ⟨simpleZeroBranch Phi p Phi' hPhi hpoint, ?_, ?_, ?_⟩
  · exact simpleZeroBranch_apply_zero Phi p Phi' hPhi hpoint
  · exact tendsto_simpleZeroBranch Phi p Phi' hPhi hpoint
  · exact eventually_simpleZeroBranch_eq_zero Phi p Phi' hzero hPhi hpoint

/-- A continuous linear equivalence in the point variables supplies the
invertibility hypothesis in `exists_simpleZeroBranch`. -/
theorem exists_simpleZeroBranch_of_pointDerivativeEquiv
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (pointDerivative : E ≃L[ℂ] E)
    (hzero : Phi (0, p) = 0)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E =
        (pointDerivative : E →L[ℂ] E)) :
    ∃ branch : ℂ → E,
      branch 0 = p ∧
      Tendsto branch (nhds 0) (nhds p) ∧
      ∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0 := by
  have hinvertible :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible := by
    rw [hpoint]
    exact ContinuousLinearMap.isInvertible_equiv
  exact exists_simpleZeroBranch Phi p Phi' hzero hPhi hinvertible

/-- The finite dimensional three variable form used for residual collision
maps. -/
theorem exists_finThreeSimpleZeroBranch
    (Phi : ℂ × (Fin 3 → ℂ) → (Fin 3 → ℂ))
    (p : Fin 3 → ℂ)
    (Phi' : ℂ × (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (pointDerivative : (Fin 3 → ℂ) ≃L[ℂ] (Fin 3 → ℂ))
    (hzero : Phi (0, p) = 0)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        (pointDerivative : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))) :
    ∃ branch : ℂ → (Fin 3 → ℂ),
      branch 0 = p ∧
      Tendsto branch (nhds 0) (nhds p) ∧
      ∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0 :=
  exists_simpleZeroBranch_of_pointDerivativeEquiv
    Phi p Phi' pointDerivative hzero hPhi hpoint

end OnLeConjecture.Analytic
