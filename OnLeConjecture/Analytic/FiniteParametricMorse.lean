/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.ParametricMorse
public import OnLeConjecture.Analytic.ParametricGermDivision
public import OnLeConjecture.Analytic.CoordinatePowerFiniteDivision
public import OnLeConjecture.Analytic.AllOrdersPreparation

/-!
# The parametric Morse lemma with finitely many parameters

The coordinate change fixes every analytic germ in the parameter
coordinates. All quotients, square roots, and inverse maps are convergent.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic.Germ

/-- The finite coordinate chain rule for arbitrary dimensions. -/
theorem partialDerivative_compPointed_sum {n m : ℕ} (q : Germ m)
    (f : PointedMapGerm n m) (i : Fin n) :
    partialDerivative i (Germ.compPointed q f) =
      ∑ j : Fin m, Germ.compPointed (partialDerivative j q) f *
        partialDerivative i (f.1.component j) := by
  rcases q with ⟨q, hq⟩
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction q using Filter.Germ.inductionOn with
  | _ q =>
      induction f using Filter.Germ.inductionOn with
      | _ f =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hq
          rw [isAnalyticMapGerm_ofFun] at hf
          change f 0 = 0 at hf0
          change partialDerivative i (Germ.compPointed (Germ.ofFunction q hq)
            (PointedMapGerm.ofFunction f hf hf0)) =
            ∑ j : Fin m, Germ.compPointed (partialDerivative j (Germ.ofFunction q hq))
              (PointedMapGerm.ofFunction f hf hf0) *
                partialDerivative i ((MapGerm.ofFunction f hf).component j)
          apply Subtype.ext
          change ((fun z ↦ fderiv ℂ (q ∘ f) z (coordinateVector i)) : FunctionGerm n) = _
          have hsum :
              (∑ j : Fin m, Germ.compPointed (partialDerivative j (Germ.ofFunction q hq))
                (PointedMapGerm.ofFunction f hf hf0) * partialDerivative i
                  ((MapGerm.ofFunction f hf).component j) : Germ n).1 =
              ((fun z ↦ ∑ j : Fin m,
                fderiv ℂ q (f z) (coordinateVector j) *
                  fderiv ℂ (fun w ↦ f w j) z (coordinateVector i)) : FunctionGerm n) := by
            change (analyticGermSubring n).subtype (∑ j : Fin m, _) = _
            rw [map_sum (analyticGermSubring n).subtype]
            change (∑ j : Fin m,
              (Filter.Germ.coeRingHom (nhds (0 : Source n)))
                (fun z ↦ fderiv ℂ q (f z) (coordinateVector j) *
                  fderiv ℂ (fun w ↦ f w j) z (coordinateVector i))) = _
            rw [← map_sum]
            exact congrArg (Filter.Germ.coeRingHom (nhds (0 : Source n))) (by
              funext z
              exact Finset.sum_apply _ _ _)
          rw [hsum]
          apply Filter.Germ.coe_eq.mpr
          have ht : Tendsto f (nhds 0) (nhds 0) := by
            simpa only [hf0] using hf.continuousAt.tendsto
          filter_upwards [hf.eventually_analyticAt,
            ht.eventually hq.eventually_analyticAt] with z hfz hqz
          rw [fderiv_comp z hqz.differentiableAt hfz.differentiableAt]
          have hdecomp : fderiv ℂ f z (coordinateVector i) =
              ∑ j : Fin m, fderiv ℂ f z (coordinateVector i) j • coordinateVector j := by
            ext j
            simp [coordinateVector, Pi.single_apply]
          change fderiv ℂ q (f z) (fderiv ℂ f z (coordinateVector i)) = _
          rw [hdecomp, map_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hcomponent : fderiv ℂ (fun w ↦ f w j) z =
              (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m ↦ ℂ) j) ∘L
                fderiv ℂ f z := by
            exact ((ContinuousLinearMap.proj (R := ℂ)
              (φ := fun _ : Fin m ↦ ℂ) j).hasFDerivAt.comp z
                hfz.differentiableAt.hasFDerivAt).fderiv
          rw [map_smul, hcomponent]
          simp [smul_eq_mul, mul_comm]

/-- An extended parameter germ has zero first partial derivative in every dimension. -/
@[simp] theorem partialDerivative_zero_hyperplaneExtension_finite {n : ℕ} (q : Germ n) :
    partialDerivative (0 : Fin (n + 1)) (hyperplaneExtension n q) = 0 := by
  change partialDerivative 0 (compPointed q (hyperplaneTailGerm n)) = 0
  rw [partialDerivative_compPointed_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hcomponent : (hyperplaneTailGerm n).1.component j = coordinate j.succ := by
    rw [← PointedMapGerm.pullback_coordinate]
    exact hyperplaneExtension_coordinate j
  rw [hcomponent, partialDerivative_coordinate_ne (Fin.succ_ne_zero j).symm, mul_zero]

/-- First differentiation of a pullback fixing all parameters has a single
chain-rule term. -/
theorem partialDerivative_zero_compPointed_of_fixes_tail {n : ℕ}
    (q : Germ (n + 1)) (f : PointedMapGerm (n + 1) (n + 1))
    (hfix : ∀ j : Fin n, f.1.component j.succ = coordinate j.succ) :
    partialDerivative 0 (compPointed q f) =
      compPointed (partialDerivative 0 q) f * partialDerivative 0 (f.1.component 0) := by
  rw [partialDerivative_compPointed_sum, Fin.sum_univ_succ]
  have hsum : (∑ j : Fin n, compPointed (partialDerivative j.succ q) f *
      partialDerivative 0 (f.1.component j.succ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hfix, partialDerivative_coordinate_ne (Fin.succ_ne_zero j).symm, mul_zero]
  rw [hsum, add_zero]

/-- The first coordinate derivative of an analytic equivalence fixing the
tail coordinates is a unit. -/
theorem first_partialDerivative_isUnit_of_equiv_fixes_tail {n : ℕ}
    (e : PointedEquivGerm (n + 1))
    (hfix : ∀ j : Fin n, e.forward.1.component j.succ = coordinate j.succ) :
    IsUnit (partialDerivative 0 (e.forward.1.component 0)) := by
  apply isUnit_of_valueRingHom_ne_zero
  intro hzero
  have hvector : e.forward.differential (coordinateVector 0) = 0 := by
    ext j
    induction j using Fin.cases with
    | zero =>
        rw [valueRingHom_partialDerivative, MapGerm.germDifferential_component,
          MapGerm.componentDifferential_apply] at hzero
        exact hzero
    | succ j =>
        have h := congrArg (fun q : Germ (n + 1) ↦ differential q (coordinateVector 0)) (hfix j)
        rw [MapGerm.germDifferential_component, MapGerm.componentDifferential_apply,
          differential_coordinate_apply] at h
        simp only [coordinateVector_apply, if_neg (Fin.succ_ne_zero j).symm] at h
        exact h
  have hinverse := congrArg (fun L : Source (n + 1) →L[ℂ] Source (n + 1) ↦
    L (coordinateVector 0)) e.differential_inverse_forward
  change e.inverse.differential (e.forward.differential (coordinateVector 0)) =
    coordinateVector 0 at hinverse
  rw [hvector, map_zero] at hinverse
  have hvalue := congrFun hinverse (0 : Fin (n + 1))
  simp [coordinateVector_apply] at hvalue

/-- An equivalence fixing extended germs fixes each tail coordinate. -/
theorem equiv_fixes_tail_of_fixes_hyperplaneExtension {n : ℕ}
    (e : PointedEquivGerm (n + 1))
    (hfix : ∀ q : Germ n, e.pullbackAlgEquiv (hyperplaneExtension n q) =
      hyperplaneExtension n q) :
    ∀ j : Fin n, e.forward.1.component j.succ = coordinate j.succ := by
  intro j
  rw [← e.forward.pullback_coordinate]
  change e.pullbackAlgEquiv (coordinate j.succ) = coordinate j.succ
  rw [← hyperplaneExtension_coordinate j]
  exact hfix _

/-- Absorb a unit multiplying a square while fixing every parameter germ. -/
theorem exists_finite_parametric_completion_of_square {n : ℕ}
    (h : Germ n) (u : Germ (n + 1)) (hu : IsUnit u) :
    ∃ e : PointedEquivGerm (n + 1),
      e.pullbackAlgEquiv (coordinate 0 ^ 2 * u + hyperplaneExtension n h) =
        coordinate 0 ^ 2 + hyperplaneExtension n h ∧
      ∀ q : Germ n, e.pullbackAlgEquiv (hyperplaneExtension n q) =
        hyperplaneExtension n q := by
  obtain ⟨v, hv, hvpow⟩ := exists_isUnit_pow_eq u hu (by decide : (2 : ℕ) ≠ 0)
  let replacement : Germ (n + 1) := coordinate 0 * v
  have hmax : replacement ∈ maximalIdeal (n + 1) :=
    (maximalIdeal (n + 1)).mul_mem_right v (coordinate_mem_maximalIdeal 0)
  have hregular : differential replacement (firstCoordinateVector n) ≠ 0 := by
    change differential replacement (coordinateVector 0) ≠ 0
    rw [← valueRingHom_partialDerivative]
    dsimp [replacement]
    rw [partialDerivative_mul, partialDerivative_coordinate_same]
    simpa using valueRingHom_ne_zero_of_isUnit hv
  obtain ⟨c, hcx, hcext⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension replacement hmax hregular
  have hcpull : c.pullbackAlgEquiv (coordinate 0 ^ 2 + hyperplaneExtension n h) =
      coordinate 0 ^ 2 * u + hyperplaneExtension n h := by
    rw [map_add, map_pow, hcx, hcext]
    dsimp only [replacement]
    rw [mul_pow, hvpow]
  refine ⟨c.symm, ?_, fun q ↦ c.symm_pullback_hyperplaneExtension_eq hcext q⟩
  have hinverse := congrArg c.pullbackAlgEquiv.symm hcpull
  rw [c.pullbackAlgEquiv.symm_apply_apply] at hinverse
  exact hinverse.symm

/-- The holomorphic Morse lemma in one distinguished variable with any
finite number of parameters, all fixed by the analytic coordinate change. -/
theorem exists_finite_parametric_morse_normal_form {n : ℕ}
    (g : Germ (n + 1)) (hg : g ∈ maximalIdeal (n + 1))
    (hfirst : valueRingHom (n + 1) (partialDerivative 0 g) = 0)
    (hsecond : valueRingHom (n + 1) (partialDerivative 0 (partialDerivative 0 g)) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1), ∃ h : Germ n,
      e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension n h ∧
      (∀ q : Germ n, e.pullbackAlgEquiv (hyperplaneExtension n q) =
        hyperplaneExtension n q) ∧ h ∈ maximalIdeal n := by
  let derivative : Germ (n + 1) := partialDerivative 0 g
  have hderivativeMax : derivative ∈ maximalIdeal (n + 1) := mem_maximalIdeal_iff.mpr hfirst
  have hregular : differential derivative (firstCoordinateVector n) ≠ 0 := by
    change differential derivative (coordinateVector 0) ≠ 0
    rw [← valueRingHom_partialDerivative]
    exact hsecond
  obtain ⟨c, hcDerivative, hcExtension⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      derivative hderivativeMax hregular
  let s : PointedEquivGerm (n + 1) := c.symm
  have hsExtension (q : Germ n) : s.pullbackAlgEquiv (hyperplaneExtension n q) =
      hyperplaneExtension n q := c.symm_pullback_hyperplaneExtension_eq hcExtension q
  have hsfix := equiv_fixes_tail_of_fixes_hyperplaneExtension s hsExtension
  have hsDerivative : s.pullbackAlgEquiv derivative = coordinate 0 := by
    have hinverse := c.pullbackRingEquiv.left_inv (coordinate 0)
    change c.inverse.pullbackRingHom (c.forward.pullbackRingHom (coordinate 0)) =
      coordinate 0 at hinverse
    have hc' : c.forward.pullbackRingHom (coordinate 0) = derivative := hcDerivative
    rw [hc'] at hinverse
    exact hinverse
  let transformed : Germ (n + 1) := s.pullbackAlgEquiv g
  let coefficient : Germ (n + 1) := partialDerivative 0 (s.forward.1.component 0)
  have htransformedDerivative : partialDerivative 0 transformed = coordinate 0 * coefficient := by
    change partialDerivative 0 (compPointed g s.forward) = _
    rw [partialDerivative_zero_compPointed_of_fixes_tail g s.forward hsfix]
    change s.pullbackAlgEquiv derivative * coefficient = _
    rw [hsDerivative]
  have hcoefficientUnit : IsUnit coefficient :=
    first_partialDerivative_isUnit_of_equiv_fixes_tail s hsfix
  let h : Germ n := hyperplaneRestriction n transformed
  obtain ⟨r, hr⟩ := exists_eq_hyperplaneExtension_add_coordinate_mul transformed
  have htransformedFactor : transformed = coordinate 0 * r + hyperplaneExtension n h := by
    exact hr.trans (add_comm _ _)
  have hidentity : coordinate 0 * coefficient = r + coordinate 0 * partialDerivative 0 r := by
    rw [← htransformedDerivative, htransformedFactor, partialDerivative_add,
      partialDerivative_mul, partialDerivative_coordinate_same,
      partialDerivative_zero_hyperplaneExtension_finite]
    ring
  have hrRestriction : hyperplaneRestriction n r = 0 := by
    have hrestricted := congrArg (hyperplaneRestriction n) hidentity
    simp only [map_add, map_mul, hyperplaneRestriction_coordinate_zero,
      zero_mul, add_zero] at hrestricted
    exact hrestricted.symm
  have hrKernel : r ∈ RingHom.ker (hyperplaneRestriction n) := hrRestriction
  rw [ker_hyperplaneRestriction_eq_span_coordinate_zero, Ideal.mem_span_singleton] at hrKernel
  obtain ⟨u, hu⟩ := hrKernel
  have hcancel : coefficient = 2 * u + coordinate 0 * partialDerivative 0 u := by
    apply mul_left_cancel₀ (coordinate_ne_zero (0 : Fin (n + 1)))
    rw [hidentity, hu, partialDerivative_mul, partialDerivative_coordinate_same]
    ring
  have huUnit : IsUnit u := by
    apply isUnit_of_valueRingHom_ne_zero
    intro huValue
    apply valueRingHom_ne_zero_of_isUnit hcoefficientUnit
    rw [hcancel]
    simp [huValue]
  have hquadratic : transformed = coordinate 0 ^ 2 * u + hyperplaneExtension n h := by
    rw [htransformedFactor, hu]
    ring
  obtain ⟨d, hdNormal, hdExtension⟩ := exists_finite_parametric_completion_of_square h u huUnit
  refine ⟨s.comp d, h, ?_, ?_, ?_⟩
  · rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change d.pullbackAlgEquiv transformed = _
    rw [hquadratic]
    exact hdNormal
  · intro q
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, hsExtension, hdExtension]
  · rw [mem_maximalIdeal_iff]
    change valueRingHom n ((hyperplaneInclusionGerm n).pullbackRingHom transformed) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    change valueRingHom (n + 1) (s.forward.pullbackRingHom g) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact mem_maximalIdeal_iff.mp hg

/-- Convergent quadratic division with any finite number of parameters. -/
theorem exists_finite_parametric_quadratic_division {n : ℕ}
    (f : Germ (n + 1)) (h : Germ n) (hh : h ∈ maximalIdeal n) :
    ∃ q : Germ (n + 1), ∃ a b : Germ n,
      f = (coordinate 0 ^ 2 + hyperplaneExtension n h) * q +
        hyperplaneExtension n a + coordinate 0 * hyperplaneExtension n b := by
  obtain ⟨F, hF, hf⟩ := exists_analyticRepresentative_allOrders f
  obtain ⟨H, hH, hhrep⟩ := exists_analyticRepresentative_allOrders h
  have hHzero : H 0 = 0 := by
    rw [mem_maximalIdeal_iff, hhrep, valueRingHom_ofFunction] at hh
    exact hh
  obtain ⟨Q, R, hQ, hR, hdivision⟩ := exists_analytic_function_coordinatePower_division
    F hF 1 (fun y ↦ -H y) hH.neg (by simp [hHzero])
  have hRi (i : Fin 2) : AnalyticAt ℂ (fun y ↦ R y i) 0 := by
    exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) i).analyticAt _ |>.comp hR
  refine ⟨ofFunction Q hQ, ofFunction (fun y ↦ R y 0) (hRi 0),
    ofFunction (fun y ↦ R y 1) (hRi 1), ?_⟩
  rw [hf, hhrep, hyperplaneExtension_ofFunction, hyperplaneExtension_ofFunction,
    hyperplaneExtension_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  change ∀ᶠ z in nhds 0,
    F z = (z 0 ^ 2 + H (hyperplaneTail n z)) * Q z +
      R (hyperplaneTail n z) 0 + z 0 * R (hyperplaneTail n z) 1
  filter_upwards [hdivision] with z hz
  simpa only [Nat.reduceAdd, sub_neg_eq_add, Fin.sum_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, one_mul, add_assoc] using hz

/-- Preparation of an analytic pair with a nondegenerate distinguished
quadratic variable. Both the coordinate change and the division remainder
are obtained from the original analytic germs. -/
theorem exists_finite_parametric_morse_pair_preparation {n : ℕ}
    (g f : Germ (n + 1)) (hg : g ∈ maximalIdeal (n + 1))
    (hfirst : valueRingHom (n + 1) (partialDerivative 0 g) = 0)
    (hsecond : valueRingHom (n + 1) (partialDerivative 0 (partialDerivative 0 g)) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1), ∃ h a b : Germ n, ∃ q : Germ (n + 1),
      e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension n h ∧
      e.pullbackAlgEquiv f = (coordinate 0 ^ 2 + hyperplaneExtension n h) * q +
        hyperplaneExtension n a + coordinate 0 * hyperplaneExtension n b ∧
      (∀ r : Germ n, e.pullbackAlgEquiv (hyperplaneExtension n r) =
        hyperplaneExtension n r) ∧ h ∈ maximalIdeal n := by
  obtain ⟨e, h, he, hfix, hh⟩ := exists_finite_parametric_morse_normal_form
    g hg hfirst hsecond
  obtain ⟨q, a, b, hdivision⟩ := exists_finite_parametric_quadratic_division
    (e.pullbackAlgEquiv f) h hh
  exact ⟨e, h, a, b, q, he, hdivision, hfix, hh⟩

end OnLeConjecture.Analytic.Germ
