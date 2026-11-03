/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSmoothPreparation
public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
public import OnLeConjecture.PlaneCurve.RegularOrderTwo
public import OnLeConjecture.PlaneCurve.QuadraticNormalization

/-!
# Node coordinates preserving a specified smooth critical curve

The node is given by two transverse analytic factors. A smooth equation
with intersection two is kept as the parameter in the Morse lemma.
Transversality forces the parameter remainder to have exact order two.
An analytic unit square root then normalizes the node while preserving
the specified curve up to multiplication by a unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

private theorem secondDerivative_value_product (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2) (i j : Fin 2) :
    valueRingHom 2 (partialDerivative i (partialDerivative j (f * g))) =
      valueRingHom 2 (partialDerivative j f) * valueRingHom 2 (partialDerivative i g) +
      valueRingHom 2 (partialDerivative i f) * valueRingHom 2 (partialDerivative j g) := by
  simp only [partialDerivative_mul, partialDerivative_add, map_add, map_mul,
    mem_maximalIdeal_iff.mp hf, mem_maximalIdeal_iff.mp hg, mul_zero, zero_mul,
    zero_add, add_zero]

/-- A product of two transverse smooth factors cannot have a square
quadratic initial form. This uses the actual second derivatives. -/
theorem transverse_product_sub_first_square_not_mem_cube
    (f g : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g)) :
    f * g - coordinate (0 : Fin 2) ^ 2 ∉ maximalIdeal 2 ^ 3 := by
  intro htail
  have hderivative (i j : Fin 2) :
      valueRingHom 2 (partialDerivative i (partialDerivative j (f * g))) =
        valueRingHom 2 (partialDerivative i
          (partialDerivative j (coordinate (0 : Fin 2) ^ 2))) := by
    apply partialDerivative_value_eq_of_sub_mem_square
    rw [← partialDerivative_sub]
    exact partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ j htail
  have hcross := hderivative 0 1
  have hyy := hderivative 1 1
  rw [secondDerivative_value_product f g hf hg] at hcross hyy
  simp only [partialDerivative_pow, partialDerivative_coordinate_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_zero, partialDerivative_zero, map_zero] at hcross hyy
  have hnonzero := valueRingHom_ne_zero_of_isUnit hjac
  rw [jacobian_eq, map_sub, map_mul, map_mul] at hnonzero
  apply hnonzero
  apply mul_self_eq_zero.mp
  linear_combination
    (valueRingHom 2 (partialDerivative 0 f) * valueRingHom 2 (partialDerivative 1 g) +
      valueRingHom 2 (partialDerivative 1 f) * valueRingHom 2 (partialDerivative 0 g)) * hcross -
    2 * valueRingHom 2 (partialDerivative 0 f) * valueRingHom 2 (partialDerivative 0 g) * hyy

private theorem hyperplaneExtension_mem_pow (r : Germ 1) (m : ℕ)
    (hr : r ∈ maximalIdeal 1 ^ m) : hyperplaneExtension 1 r ∈ maximalIdeal 2 ^ m := by
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hr
  obtain ⟨q, hq⟩ := hr
  rw [hq, map_mul, map_pow, hyperplaneExtension_coordinate]
  exact (maximalIdeal 2 ^ m).mul_mem_right _ (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal _) m)

/-- The parameter remainder in a transverse node Morse form has exact
order two. The order is proved, not supplied with the Morse expression. -/
theorem node_morse_remainder_exact_order_two
    (f g : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g)) (r : Germ 1)
    (hform : f * g = coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r) :
    r ∈ maximalIdeal 1 ^ 2 ∧ r ∉ maximalIdeal 1 ^ 3 := by
  have hproduct : f * g ∈ maximalIdeal 2 ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hf hg
  have hrestriction : hyperplaneRestriction 1 (f * g) = r := by
    rw [hform, map_add, map_pow, hyperplaneRestriction_coordinate_zero, zero_pow (by decide),
      zero_add]
    exact DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) r
  constructor
  · have h := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow hproduct
    change hyperplaneRestriction 1 (f * g) ∈ maximalIdeal 1 ^ 2 at h
    rwa [hrestriction] at h
  · intro hr
    apply transverse_product_sub_first_square_not_mem_cube f g hf hg hjac
    rw [hform, add_sub_cancel_left]
    exact hyperplaneExtension_mem_pow r 3 hr

/-- A parameter remainder of exact order two admits a convergent square
normalization. The first coordinate is fixed, and the second coordinate
changes by an explicitly produced analytic unit. -/
theorem exists_node_parameter_square_normalization (r : Germ 1)
    (hr : r ∈ maximalIdeal 1 ^ 2) (hnext : r ∉ maximalIdeal 1 ^ 3) :
    ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r) =
        coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2 ∧
      e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) ∧
      e.pullbackAlgEquiv (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) * U := by
  have hrne : r ≠ 0 := fun hz => hnext (hz ▸ (maximalIdeal 1 ^ 3).zero_mem)
  obtain ⟨k, u, hu, hru⟩ := exists_eq_coordinate_pow_mul_unit hrne
  have horder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hru
  have hk2 : k = 2 := by
    rw [mem_maximalIdeal_one_pow_iff, horder] at hr hnext
    norm_cast at hr hnext
    omega
  subst k
  obtain ⟨w, hw, hwpow⟩ := exists_isUnit_pow_eq (-u) hu.neg (by decide : (2 : ℕ) ≠ 0)
  let V := hyperplaneExtension 1 w
  have hV : IsUnit V := hw.map (hyperplaneExtension 1)
  let parameter := coordinate (1 : Fin 2) * V
  have hparameter : parameter ∈ maximalIdeal 2 :=
    (maximalIdeal 2).mul_mem_right V (coordinate_mem_maximalIdeal 1)
  have hregular : valueRingHom 2 (partialDerivative (1 : Fin 2) parameter) ≠ 0 := by
    change valueRingHom 2 (partialDerivative (1 : Fin 2) (coordinate (1 : Fin 2) * V)) ≠ 0
    rw [partialDerivative_mul, partialDerivative_coordinate_same]
    simpa using valueRingHom_ne_zero_of_isUnit hV
  obtain ⟨c, hc1, hc0⟩ := PlaneCurve.exists_equiv_pullback_coordinate_one_eq_preserving_zero
    parameter hparameter hregular
  have hparameterPow : parameter ^ 2 = -hyperplaneExtension 1 r := by
    dsimp only [parameter, V]
    rw [mul_pow, ← map_pow, hwpow, map_neg, hru, map_mul, map_pow, hyperplaneExtension_coordinate]
    change coordinate (1 : Fin 2) ^ 2 * -hyperplaneExtension 1 u =
      -(coordinate (1 : Fin 2) ^ 2 * hyperplaneExtension 1 u)
    ring
  have hc : c.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2) =
      coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r := by
    rw [map_sub, map_pow, map_pow, hc0, hc1, hparameterPow, sub_neg_eq_add]
  let e := c.symm
  have he : e.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r) =
      coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2 := by
    have h := congrArg c.pullbackAlgEquiv.symm hc
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact h.symm
  have he0 : e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) := by
    have h := congrArg c.pullbackAlgEquiv.symm hc0
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact h.symm
  have heparameter : e.pullbackAlgEquiv (coordinate (1 : Fin 2)) * e.pullbackAlgEquiv V =
      coordinate (1 : Fin 2) := by
    have h := congrArg c.pullbackAlgEquiv.symm hc1
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact (map_mul e.pullbackAlgEquiv _ _).symm.trans h.symm
  obtain ⟨v, hv⟩ := hV.map e.pullbackAlgEquiv.toRingHom
  change (v : Germ 2) = e.pullbackAlgEquiv V at hv
  refine ⟨e, ↑v⁻¹, (v⁻¹).isUnit, he, he0, ?_⟩
  rw [← hv] at heparameter
  calc
    e.pullbackAlgEquiv (coordinate (1 : Fin 2)) =
      (e.pullbackAlgEquiv (coordinate (1 : Fin 2)) * ↑v) * ↑v⁻¹ := by simp
    _ = coordinate (1 : Fin 2) * ↑v⁻¹ := by rw [heparameter]

/-- Simultaneous node normalization and preservation of the specified
smooth curve, from its actual intersection number and the transverse
analytic factorization of the node. -/
theorem exists_smooth_critical_node_normalization
    (v h f g : Germ 2) (hfactor : v = f * g)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g))
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2) :
    ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.forward.pullbackRingHom v = coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2 ∧
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U := by
  obtain ⟨a, ha, hregular⟩ := exists_smooth_second_coordinate_regular_first
    h v hh hdh hfinite 2 hi
  obtain ⟨b, r, hform, _hfix, hb1, _hrmax⟩ :=
    PlaneCurve.exists_parametric_morse_normal_form_of_regular_order_two
      (a.forward.pullbackRingHom v) hregular
  let e₀ := a.comp b
  have he₀h : e₀.pullbackAlgEquiv h = coordinate (1 : Fin 2) := by
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change b.pullbackAlgEquiv (a.forward.pullbackRingHom h) = _
    rw [ha]
    exact (b.forward.pullback_coordinate (1 : Fin 2)).trans hb1
  have he₀v : e₀.pullbackAlgEquiv v = coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r := by
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    exact hform
  let F := e₀.pullbackAlgEquiv f
  let G := e₀.pullbackAlgEquiv g
  have hF : F ∈ maximalIdeal 2 := e₀.forward.pullback_mem_maximalIdeal hf
  have hG : G ∈ maximalIdeal 2 := e₀.forward.pullback_mem_maximalIdeal hg
  have hFGjac : IsUnit (jacobian F G) := jacobian_isUnit_pullback_equiv e₀ f g hjac
  have hFGform : F * G = coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r := by
    rw [hfactor, map_mul] at he₀v
    exact he₀v
  obtain ⟨hr, hnext⟩ := node_morse_remainder_exact_order_two F G hF hG hFGjac r hFGform
  obtain ⟨c, U, hU, hcform, _hcx, hcy⟩ := exists_node_parameter_square_normalization r hr hnext
  refine ⟨e₀.comp c, U, hU, ?_, ?_⟩
  · change (e₀.comp c).pullbackAlgEquiv v = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, he₀v]
    exact hcform
  · change (e₀.comp c).pullbackAlgEquiv h = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, he₀h]
    exact hcy

/-- The convergent factorization theorem supplies the factorization input
when the node is given by its ordinary quadratic initial form. -/
theorem exists_smooth_critical_node_normalization_of_quadratic_tail
    (v h : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2) :
    ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.forward.pullbackRingHom v = coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2 ∧
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U := by
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := exists_transverse_node_factorization v α β hβ hv
  exact exists_smooth_critical_node_normalization v h f g hfactor hf hg hjac hh hdh hfinite hi

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.PointedEquivGerm

/-- Preservation of a critical equation up to a unit suffices to transport
every power dividing a Jacobian to the corresponding coordinate power.
Only the displayed factorization is needed for this direction. -/
theorem coordinate_pow_dvd_jacobian_of_pullback_multiple
    (e : PointedEquivGerm 2) (h f g U : Germ 2) (k : ℕ)
    (he : e.forward.pullbackRingHom h = Germ.coordinate (1 : Fin 2) * U)
    (hdiv : h ^ k ∣ Germ.jacobian f g) :
    Germ.coordinate (1 : Fin 2) ^ k ∣
      Germ.jacobian (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) := by
  have hpull := map_dvd e.forward.pullbackRingHom hdiv
  rw [map_pow, he, mul_pow] at hpull
  have hcoordinate : Germ.coordinate (1 : Fin 2) ^ k ∣
      e.forward.pullbackRingHom (Germ.jacobian f g) :=
    (dvd_mul_right _ _).trans hpull
  rw [show Germ.jacobian (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) =
      e.forward.pullbackRingHom (Germ.jacobian f g) * Germ.coordinateJacobian e.forward from
        Germ.jacobian_compPointed f g e.forward]
  exact dvd_mul_of_dvd_left hcoordinate _

end OnLeConjecture.Analytic.PointedEquivGerm
