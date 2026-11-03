/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.Milnor
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import OnLeConjecture.Analytic.OrderOnePreparation
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.PlaneCurve.SmoothStraightening

/-!
# The quantity μ + b - 1 for nonunit plane equations

The definition below uses Jacobian colength and the number of distinct
irreducible factors. Unit equations are assigned zero. For reduced
nonunit equations the Jacobian colength is finite, and this is the
quantity occurring in the plane-curve Milnor formula.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ UniqueFactorizationMonoid

/-- Every nonzero nonunit analytic plane equation has at least one
irreducible branch. -/
theorem irreducibleBranchCount_pos_of_nonzero_nonunit
    (f : Germ 2) (hf : f ≠ 0) (hu : ¬ IsUnit f) : 0 < irreducibleBranchCount f := by
  classical
  rw [irreducibleBranchCount, Finset.card_pos]
  have hne : normalizedFactors (Associates.mk f) ≠ 0 := by
    intro hz
    have hunit := (normalizedFactors_eq_zero_iff (Associates.mk_ne_zero.mpr hf)).mp hz
    exact hu (Associates.isUnit_mk.mp hunit)
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hne
  exact ⟨p, Multiset.mem_toFinset.mpr hp⟩

/-- The Jacobian colength plus branch count minus one for a nonunit
equation. The value is zero for a unit equation. -/
@[expose] noncomputable def milnorBranchDefect (f : Germ 2) : ℕ := by
  classical
  exact if IsUnit f then 0 else
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + irreducibleBranchCount f - 1

theorem milnorBranchDefect_eq_zero_of_isUnit
    (f : Germ 2) (hf : IsUnit f) : milnorBranchDefect f = 0 := by
  simp only [milnorBranchDefect, if_pos hf]

theorem milnorBranchDefect_add_one
    (f : Germ 2) (hf : f ≠ 0) (hu : ¬ IsUnit f) :
    milnorBranchDefect f + 1 =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + irreducibleBranchCount f := by
  have hb := irreducibleBranchCount_pos_of_nonzero_nonunit f hf hu
  simp only [milnorBranchDefect, if_neg hu]
  omega

theorem milnorBranchDefect_add_one_eq_milnorNumber
    (f : Germ 2) (hf : f ≠ 0) (hu : ¬ IsUnit f) (h : HasIsolatedCriticalPoint f) :
    milnorBranchDefect f + 1 = milnorNumber f h + irreducibleBranchCount f :=
  milnorBranchDefect_add_one f hf hu

/-- Jacobian colength is invariant under analytic coordinate changes,
without a critical-point hypothesis. -/
theorem jacobianColength_pullback (e : PointedEquivGerm 2) (f : Germ 2) :
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (e.forward.pullbackRingHom f)) := by
  exact (Ideal.quotientEquivAlg (jacobianIdeal f)
    (jacobianIdeal (e.pullbackAlgEquiv f)) e.pullbackAlgEquiv
    (map_jacobianIdeal_pullbackAlgEquiv e f).symm).toLinearEquiv.finrank_eq

/-- Analytic source equivalences preserve the Milnor branch quantity. -/
theorem milnorBranchDefect_pullback (e : PointedEquivGerm 2) (f : Germ 2) :
    milnorBranchDefect f = milnorBranchDefect (e.forward.pullbackRingHom f) := by
  classical
  have hunit : IsUnit (e.forward.pullbackRingHom f) ↔ IsUnit f :=
    MulEquiv.isUnit_map e.pullbackRingEquiv
  simp only [milnorBranchDefect, hunit, jacobianColength_pullback e f,
    irreducibleBranchCount_pullback e f]

/-- An order-one equation has zero Jacobian colength. -/
theorem jacobianColength_eq_zero_of_order_one
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) = 0 := by
  obtain ⟨e, he⟩ := exists_equiv_pullback_eq_coordinate f hf
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).1
  have hcoordinate : e.forward.pullbackRingHom f = coordinate (0 : Fin 2) := he
  rw [jacobianColength_pullback e f, hcoordinate]
  have htop : jacobianIdeal (coordinate (0 : Fin 2)) = ⊤ := by
    rw [jacobianIdeal, partialDerivative_coordinate_same]
    apply Ideal.eq_top_of_isUnit_mem (x := (1 : Germ 2))
    · exact Ideal.subset_span (by simp)
    · exact isUnit_one
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

/-- An order-one equation has one branch and zero Milnor branch quantity. -/
theorem milnorBranchDefect_eq_zero_of_order_one
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hn : f ∉ maximalIdeal 2 ^ 2) :
    milnorBranchDefect f = 0 := by
  have hirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).2
  rw [milnorBranchDefect, if_neg hirr.not_isUnit,
    jacobianColength_eq_zero_of_order_one f hf hn,
    irreducibleBranchCount_eq_one_of_irreducible f hirr]

end OnLeConjecture.PlaneCurve
