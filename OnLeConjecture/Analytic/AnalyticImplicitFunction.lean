/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SimpleZeroPersistence
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Analytic implicit branches

The implicit branch used for persistence of a simple zero is analytic when
the defining map is analytic.
-/

public section

open scoped ContDiff

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The implicit branch of an analytic equation, with an arbitrary complex
Banach space of parameters. -/
@[expose]
noncomputable def analyticImplicitBranch
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (Phi : P × E → E) (s : P × E)
    (hPhi : AnalyticAt ℂ Phi s)
    (hpoint :
      (fderiv ℂ Phi s ∘L ContinuousLinearMap.inr ℂ P E).IsInvertible) :
    P → E :=
  hPhi.hasStrictFDerivAt.implicitFunctionOfProdDomain hpoint

/-- The analytic implicit branch passes through the base point. -/
@[simp]
theorem analyticImplicitBranch_apply_base
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (Phi : P × E → E) (s : P × E)
    (hPhi : AnalyticAt ℂ Phi s)
    (hpoint :
      (fderiv ℂ Phi s ∘L ContinuousLinearMap.inr ℂ P E).IsInvertible) :
    analyticImplicitBranch Phi s hPhi hpoint s.1 = s.2 := by
  have hbase :=
    (hPhi.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hpoint).self_of_nhds
  simpa [analyticImplicitBranch] using hbase.mp rfl

/-- The analytic implicit branch solves the equation near the base
parameter. -/
theorem eventually_analyticImplicitBranch_eq
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (Phi : P × E → E) (s : P × E)
    (hPhi : AnalyticAt ℂ Phi s)
    (hpoint :
      (fderiv ℂ Phi s ∘L ContinuousLinearMap.inr ℂ P E).IsInvertible) :
    ∀ᶠ p in nhds s.1,
      Phi (p, analyticImplicitBranch Phi s hPhi hpoint p) = Phi s := by
  simpa [analyticImplicitBranch] using
    hPhi.hasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain hpoint

/-- The implicit branch of an analytic equation is analytic. -/
theorem analyticAt_analyticImplicitBranch
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (Phi : P × E → E) (s : P × E)
    (hPhi : AnalyticAt ℂ Phi s)
    (hpoint :
      (fderiv ℂ Phi s ∘L ContinuousLinearMap.inr ℂ P E).IsInvertible) :
    AnalyticAt ℂ (analyticImplicitBranch Phi s hPhi hpoint) s.1 := by
  let hContDiff : ContDiffAt ℂ ω Phi s := hPhi.contDiffAt
  have hBranch : ContDiffAt ℂ ω
      (hContDiff.implicitFunction (by simp) hpoint) s.1 :=
    hContDiff.contDiffAt_implicitFunction (by simp) hpoint
  have hEq : analyticImplicitBranch Phi s hPhi hpoint =
      hContDiff.implicitFunction (by simp) hpoint := by
    simp only [analyticImplicitBranch, ContDiffAt.implicitFunction_def]
  rw [hEq]
  exact hBranch.analyticAt

/-- The branch supplied by the implicit function theorem is analytic at the
base parameter when the implicit equation is analytic there. -/
theorem analyticAt_simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (Phi' : ℂ × E →L[ℂ] E)
    (hPhi : HasStrictFDerivAt Phi Phi' (0, p))
    (hpoint : (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ E).IsInvertible)
    (hAnalytic : AnalyticAt ℂ Phi (0, p)) :
    AnalyticAt ℂ (simpleZeroBranch Phi p Phi' hPhi hpoint) 0 := by
  have hPhi' : Phi' = fderiv ℂ Phi (0, p) := hPhi.hasFDerivAt.fderiv.symm
  subst Phi'
  let hContDiff : ContDiffAt ℂ ω Phi (0, p) := hAnalytic.contDiffAt
  have hBranch : ContDiffAt ℂ ω
      (hContDiff.implicitFunction (by simp) hpoint) 0 := by
    simpa using hContDiff.contDiffAt_implicitFunction (by simp) hpoint
  have hEq :
      simpleZeroBranch Phi p (fderiv ℂ Phi (0, p)) hPhi hpoint =
        hContDiff.implicitFunction (by simp) hpoint := by
    simp only [simpleZeroBranch, ContDiffAt.implicitFunction_def]
  rw [hEq]
  exact hBranch.analyticAt

/-- An analytic equation with an invertible point derivative has an analytic
local zero branch. -/
theorem exists_analytic_simpleZeroBranch
    (Phi : ℂ × E → E) (p : E)
    (hzero : Phi (0, p) = 0)
    (hAnalytic : AnalyticAt ℂ Phi (0, p))
    (hpoint :
      (fderiv ℂ Phi (0, p) ∘L
        ContinuousLinearMap.inr ℂ ℂ E).IsInvertible) :
    ∃ branch : ℂ → E,
      AnalyticAt ℂ branch 0 ∧
      branch 0 = p ∧
      ∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0 := by
  let hPhi := hAnalytic.hasStrictFDerivAt
  refine ⟨simpleZeroBranch Phi p (fderiv ℂ Phi (0, p)) hPhi hpoint,
    analyticAt_simpleZeroBranch Phi p (fderiv ℂ Phi (0, p)) hPhi hpoint hAnalytic,
    simpleZeroBranch_apply_zero Phi p (fderiv ℂ Phi (0, p)) hPhi hpoint, ?_⟩
  exact eventually_simpleZeroBranch_eq_zero Phi p (fderiv ℂ Phi (0, p))
    hzero hPhi hpoint

end OnLeConjecture.Analytic
