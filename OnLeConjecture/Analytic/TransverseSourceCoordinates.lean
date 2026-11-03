/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneJacobianInverse
public import OnLeConjecture.Analytic.TransverseJacobianOrder

/-!
# Source coordinates adapted to a curve and a transverse section

A parameter with nonzero derivative on the curve tangent and a smooth
curve equation form analytic coordinates. Applying the coordinate change
to the three Jacobian minors preserves their exact common factor, up to
an analytic unit. This connects their local factor order to the order of
the constructed transverse parametrization.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.Germ

/-- Two pointed germs with unit Jacobian form simultaneous analytic
coordinates. The inverse coordinate map is constructed analytically. -/
theorem exists_equiv_pullback_pair_eq_coordinates
    (f p : Germ 2) (hf : f ∈ maximalIdeal 2) (hp : p ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f p)) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom f = coordinate 0 ∧
      e.forward.pullbackRingHom p = coordinate 1 := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  obtain ⟨P, hP, rfl⟩ := exists_ofFunction p
  have hF0 : F 0 = 0 := (mem_maximalIdeal_iff.mp hf)
  have hP0 : P 0 = 0 := (mem_maximalIdeal_iff.mp hp)
  let R : Source 2 → Source 2 := fun z => ![F z, P z]
  have hR : AnalyticAt ℂ R 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hF
    · exact hP
  have hR0 : R 0 = 0 := by ext i; fin_cases i <;> simp only [R, hF0, hP0] <;> rfl
  let r := PointedMapGerm.ofFunction R hR hR0
  have hr0 : r.1.component 0 = ofFunction F hF := by apply Subtype.ext; rfl
  have hr1 : r.1.component 1 = ofFunction P hP := by apply Subtype.ext; rfl
  have hrjac : IsUnit (coordinateJacobian r) := by
    simpa only [coordinateJacobian, hr0, hr1] using hjac
  obtain ⟨e, he⟩ := r.exists_pointedEquivGerm_of_coordinateJacobian_isUnit hrjac
  have hinv : r.comp e.inverse = PointedMapGerm.identity 2 := he ▸ e.forward_inverse
  have hcoord (i : Fin 2) := congrArg (fun q : PointedMapGerm 2 2 =>
    q.pullbackRingHom (coordinate i)) hinv
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    PointedMapGerm.pullback_coordinate, PointedMapGerm.pullbackRingHom_identity,
    RingHom.id_apply] at hcoord
  exact ⟨e.symm, by simpa only [PointedEquivGerm.symm, hr0] using hcoord 0,
    by simpa only [PointedEquivGerm.symm, hr1] using hcoord 1⟩

/-- A smooth equation and a function nonconstant on its tangent have
unit Jacobian. -/
theorem jacobian_isUnit_of_transverse_tangent
    (f p : Germ 2) (v : Source 2)
    (hp : differential p ≠ 0) (hpv : differential p v = 0)
    (hfv : differential f v ≠ 0) : IsUnit (jacobian f p) := by
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  intro hj
  have hdet : differential f (coordinateVector 0) * differential p (coordinateVector 1) -
      differential f (coordinateVector 1) * differential p (coordinateVector 0) = 0 := by
    simpa only [jacobian_eq, map_sub, map_mul, valueRingHom_partialDerivative] using hj
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 := by
    ext i
    fin_cases i <;> simp
  have hexp (q : Germ 2) : differential q v =
      v 0 * differential q (coordinateVector 0) + v 1 * differential q (coordinateVector 1) := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
    rfl
  have hp0 : differential p (coordinateVector 0) = 0 := by
    have hprod : differential f v * differential p (coordinateVector 0) = 0 := by
      rw [hexp f]
      rw [hexp p] at hpv
      linear_combination differential f (coordinateVector 0) * hpv - v 1 * hdet
    exact (mul_eq_zero.mp hprod).resolve_left hfv
  have hp1 : differential p (coordinateVector 1) = 0 := by
    have hprod : differential f v * differential p (coordinateVector 1) = 0 := by
      rw [hexp f]
      rw [hexp p] at hpv
      linear_combination differential f (coordinateVector 1) * hpv + v 0 * hdet
    exact (mul_eq_zero.mp hprod).resolve_left hfv
  apply hp
  ext z
  have hz : z = z 0 • coordinateVector 0 + z 1 • coordinateVector 1 := by
    ext i
    fin_cases i <;> simp
  rw [hz, map_add, map_smul, map_smul, hp0, hp1, smul_zero, smul_zero, add_zero]
  rfl

/-- Tangent transversality constructs simultaneous analytic coordinates
for the parameter and the smooth curve equation. -/
theorem exists_equiv_pullback_pair_of_transverse_tangent
    (f p : Germ 2) (hf : f ∈ maximalIdeal 2) (hp : p ∈ maximalIdeal 2)
    (v : Source 2) (hdp : differential p ≠ 0)
    (hpv : differential p v = 0) (hfv : differential f v ≠ 0) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom f = coordinate 0 ∧
      e.forward.pullbackRingHom p = coordinate 1 :=
  exists_equiv_pullback_pair_eq_coordinates f p hf hp
    (jacobian_isUnit_of_transverse_tangent f p v hdp hpv hfv)

/-- After constructing coordinates from a transverse parameter and a
smooth common-divisor curve, the order of the transverse pair is the
common-minor exponent plus one. -/
theorem exists_transverse_coordinates_and_order_of_jacobian_factors
    (f a b p u v w : Germ 2) (k : ℕ)
    (hf : f ∈ maximalIdeal 2) (ha : a ∈ maximalIdeal 2)
    (hb : b ∈ maximalIdeal 2) (hp : p ∈ maximalIdeal 2)
    (hfp : IsUnit (jacobian f p))
    (hfa : jacobian f a = p ^ k * u)
    (hfb : jacobian f b = p ^ k * v)
    (hab : jacobian a b = p ^ k * w)
    (hunit : IsUnit u ∨ IsUnit v ∨ IsUnit w) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom f = coordinate 0 ∧
      e.forward.pullbackRingHom p = coordinate 1 ∧
      min (vanishingOrder (hyperplaneRestriction 1 (e.forward.pullbackRingHom a)))
        (vanishingOrder (hyperplaneRestriction 1 (e.forward.pullbackRingHom b))) =
          (k + 1 : ℕ) := by
  obtain ⟨e, hef, hep⟩ := exists_equiv_pullback_pair_eq_coordinates f p hf hp hfp
  let J := coordinateJacobian e.forward
  have hJ : IsUnit J := Germ.PointedEquivGerm.coordinateJacobian_isUnit e
  have hfactor (r s z : Germ 2) (h : jacobian r s = p ^ k * z) :
      jacobian (e.forward.pullbackRingHom r) (e.forward.pullbackRingHom s) =
        coordinate (1 : Fin 2) ^ k * (e.forward.pullbackRingHom z * J) := by
    change jacobian (compPointed r e.forward) (compPointed s e.forward) = _
    rw [jacobian_compPointed]
    change e.forward.pullbackRingHom (jacobian r s) * J = _
    rw [h, map_mul, map_pow, hep, mul_assoc]
  have hua : IsUnit (e.forward.pullbackRingHom u * J) ∨
      IsUnit (e.forward.pullbackRingHom v * J) ∨
      IsUnit (e.forward.pullbackRingHom w * J) := by
    rcases hunit with hu | hv | hw
    · exact Or.inl ((hu.map e.forward.pullbackRingHom).mul hJ)
    · exact Or.inr (Or.inl ((hv.map e.forward.pullbackRingHom).mul hJ))
    · exact Or.inr (Or.inr ((hw.map e.forward.pullbackRingHom).mul hJ))
  refine ⟨e, hef, hep, ?_⟩
  apply min_transverse_orders_eq_of_three_jacobian_factors
    (e.forward.pullbackRingHom a) (e.forward.pullbackRingHom b)
    (e.forward.pullbackRingHom u * J) (e.forward.pullbackRingHom v * J)
    (e.forward.pullbackRingHom w * J) k
    (e.forward.pullback_mem_maximalIdeal ha) (e.forward.pullback_mem_maximalIdeal hb)
    (by simpa only [hef] using hfactor f a u hfa)
    (by simpa only [hef] using hfactor f b v hfb)
    (hfactor a b w hab) hua

end OnLeConjecture.Analytic.Germ
