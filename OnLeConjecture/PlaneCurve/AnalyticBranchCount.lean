/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic.NormNum

/-!
# The number of irreducible analytic branches

The branch count is the number of distinct irreducible associate classes
in a plane analytic germ. The proved UFD instance supplies the factors.
Multiplicities of factors are ignored, as required for branch counting.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic UniqueFactorizationMonoid

/-- The number of distinct irreducible analytic factors, up to units.
The zero germ is assigned count zero. -/
@[expose] noncomputable def irreducibleBranchCount (f : Germ 2) : ℕ := by
  classical
  exact (normalizedFactors (Associates.mk f)).toFinset.card

@[simp] theorem irreducibleBranchCount_zero : irreducibleBranchCount 0 = 0 := by
  simp [irreducibleBranchCount]

@[simp] theorem irreducibleBranchCount_one : irreducibleBranchCount 1 = 0 := by
  simp [irreducibleBranchCount]

theorem irreducibleBranchCount_eq_of_associated {f g : Germ 2} (h : Associated f g) :
    irreducibleBranchCount f = irreducibleBranchCount g := by
  unfold irreducibleBranchCount
  rw [Associates.mk_eq_mk_iff_associated.mpr h]

/-- Two nonassociated irreducible analytic factors give exactly two
branches. This follows from UFD factorization, not an assumed branch count. -/
theorem irreducibleBranchCount_eq_two_of_eq_mul
    (v f g : Germ 2) (hf : Irreducible f) (hg : Irreducible g)
    (hne : ¬ Associated f g) (hfactor : v = f * g) : irreducibleBranchCount v = 2 := by
  classical
  have hf' : Irreducible (Associates.mk f) := Associates.irreducible_mk.mpr hf
  have hg' : Irreducible (Associates.mk g) := Associates.irreducible_mk.mpr hg
  have hne' : Associates.mk f ≠ Associates.mk g := Associates.mk_eq_mk_iff_associated.not.mpr hne
  rw [irreducibleBranchCount, hfactor, ← Associates.mk_mul_mk,
    normalizedFactors_mul hf'.ne_zero hg'.ne_zero,
    normalizedFactors_irreducible hf', normalizedFactors_irreducible hg']
  simp [normalize_eq, hne']

end OnLeConjecture.PlaneCurve
