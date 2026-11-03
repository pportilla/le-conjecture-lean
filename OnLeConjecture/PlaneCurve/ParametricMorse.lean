/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.Analytic.Dimension
public import OnLeConjecture.Analytic.SmoothDivision
public import OnLeConjecture.Analytic.UnitRoot

/-!
# The parametric Morse lemma for plane analytic germs

This file proves the analytic completion of the square while leaving the
second coordinate fixed. It then derives the parametric Morse normal form
from a nonzero second derivative in the first coordinate direction.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Replacing the first coordinate does not change the remaining
coordinates. -/
theorem hyperplaneTail_firstCoordinateReplacement {n : ℕ}
    (f : Source (n + 1) → ℂ) (z : Source (n + 1)) :
    hyperplaneTail n (firstCoordinateReplacement f z) =
      hyperplaneTail n z := by
  ext i
  simp [hyperplaneTail]

/-- Extension sends a coordinate on the hyperplane to the corresponding
tail coordinate. -/
@[simp]
theorem hyperplaneExtension_coordinate {n : ℕ} (i : Fin n) :
    Germ.hyperplaneExtension n (Germ.coordinate i) =
      Germ.coordinate i.succ := by
  rw [Germ.hyperplaneExtension, PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  change
    ((MapGerm.ofFunction (hyperplaneTail n)
      ((hyperplaneTail n).analyticAt 0)).component i).1 =
      (Germ.coordinate i.succ).1
  rw [MapGerm.component_ofFunction]
  rfl

/-- A germ regular in the first coordinate can be made the first coordinate
by an analytic equivalence which fixes every germ in the remaining
coordinates. -/
theorem exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
    {n : ℕ} (g : Germ (n + 1)) (hg : g ∈ Germ.maximalIdeal (n + 1))
    (hregular : Germ.differential g (firstCoordinateVector n) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1),
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin (n + 1))) = g ∧
        ∀ q : Germ n,
          e.pullbackAlgEquiv (Germ.hyperplaneExtension n q) =
            Germ.hyperplaneExtension n q := by
  rcases g with ⟨g, hgan⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hgan
      have hf0 : f 0 = 0 := by
        rw [Germ.mem_maximalIdeal_iff] at hg
        change Filter.Germ.value (f : FunctionGerm (n + 1)) = 0 at hg
        simpa only [Filter.Germ.value_ofFun] using hg
      change fderiv ℂ f 0 (firstCoordinateVector n) ≠ 0 at hregular
      let F : Source (n + 1) → Source (n + 1) :=
        firstCoordinateReplacement f
      have hF : AnalyticAt ℂ F 0 :=
        firstCoordinateReplacement_analyticAt hgan
      have hF0 : F 0 = 0 := firstCoordinateReplacement_zero hf0
      let p : PointedMapGerm (n + 1) (n + 1) :=
        PointedMapGerm.ofFunction F hF hF0
      have hinjective : Function.Injective p.differential := by
        change Function.Injective (fderiv ℂ F 0)
        exact fderiv_firstCoordinateReplacement_injective
          hgan.differentiableAt hregular
      have hbijective : Function.Bijective p.differential :=
        ⟨hinjective, LinearMap.surjective_of_injective hinjective⟩
      rcases p.exists_pointedEquivGerm_of_differential_bijective
          hbijective with ⟨e, he⟩
      refine ⟨e, ?_, ?_⟩
      · rw [PointedEquivGerm.pullbackAlgEquiv_apply,
          PointedEquivGerm.pullbackRingEquiv_apply, he,
          PointedMapGerm.pullback_coordinate]
        apply Subtype.ext
        change ((MapGerm.ofFunction F hF).component 0).1 = _
        rw [MapGerm.component_ofFunction]
        rfl
      · intro q
        rcases q with ⟨q, hq⟩
        induction q using Filter.Germ.inductionOn with
        | _ q =>
            rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hq
            rw [PointedEquivGerm.pullbackAlgEquiv_apply,
              PointedEquivGerm.pullbackRingEquiv_apply, he]
            change Germ.compPointed
                (Germ.hyperplaneExtension n (Germ.ofFunction q hq)) p =
              Germ.hyperplaneExtension n (Germ.ofFunction q hq)
            rw [Germ.hyperplaneExtension_ofFunction]
            apply Subtype.ext
            apply Filter.Germ.coe_eq.mpr
            filter_upwards [] with z
            change q (hyperplaneTail n (F z)) = q (hyperplaneTail n z)
            rw [hyperplaneTail_firstCoordinateReplacement]

/-- In the preceding equivalence, each remaining coordinate is fixed. -/
theorem exists_equiv_pullback_coordinate_eq_preserving_tail
    {n : ℕ} (g : Germ (n + 1)) (hg : g ∈ Germ.maximalIdeal (n + 1))
    (hregular : Germ.differential g (firstCoordinateVector n) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1),
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin (n + 1))) = g ∧
        ∀ i : Fin n,
          e.pullbackAlgEquiv (Germ.coordinate i.succ) =
            Germ.coordinate i.succ := by
  obtain ⟨e, he0, hext⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      g hg hregular
  refine ⟨e, he0, ?_⟩
  intro i
  have hi := hext (Germ.coordinate i)
  rw [hyperplaneExtension_coordinate] at hi
  exact hi

/-- Differentiating an extended germ in the omitted coordinate gives zero.
-/
@[simp]
theorem partialDerivative_zero_hyperplaneExtension
    (q : Germ 1) :
    Germ.partialDerivative (0 : Fin 2) (Germ.hyperplaneExtension 1 q) = 0 := by
  rcases q with ⟨q, hq⟩
  induction q using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hq
      change Germ.partialDerivative (0 : Fin 2)
        (Germ.hyperplaneExtension 1 (Germ.ofFunction f hq)) = 0
      rw [Germ.hyperplaneExtension_ofFunction]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      have htail : Tendsto (hyperplaneTail 1) (𝓝 (0 : Source 2))
          (𝓝 (0 : Source 1)) := by
        have hc := (hyperplaneTail 1).continuous.continuousAt
          (x := (0 : Source 2))
        change Tendsto (hyperplaneTail 1) (𝓝 (0 : Source 2))
          (𝓝 (hyperplaneTail 1 0)) at hc
        simpa only [map_zero] using hc
      filter_upwards [htail.eventually hq.eventually_analyticAt] with z hz
      change fderiv ℂ (f ∘ hyperplaneTail 1) z
          (coordinateVector (0 : Fin 2)) = 0
      rw [fderiv_comp z hz.differentiableAt
        (hyperplaneTail 1).differentiableAt]
      rw [ContinuousLinearMap.fderiv]
      change fderiv ℂ f (hyperplaneTail 1 z)
          (hyperplaneTail 1 (coordinateVector (0 : Fin 2))) = 0
      have hzero :
          hyperplaneTail 1 (coordinateVector (0 : Fin 2)) = 0 := by
        ext i
        fin_cases i
        simp [hyperplaneTail, coordinateVector_apply]
      rw [hzero, map_zero]

end Germ

namespace PointedEquivGerm

/-- Composition of pointed analytic equivalence germs. -/
@[expose] noncomputable def comp {n : ℕ} (e f : PointedEquivGerm n) :
    PointedEquivGerm n where
  forward := e.forward.comp f.forward
  inverse := f.inverse.comp e.inverse
  forward_inverse := by
    calc
      (e.forward.comp f.forward).comp (f.inverse.comp e.inverse) =
          e.forward.comp (f.forward.comp (f.inverse.comp e.inverse)) := by
        rw [PointedMapGerm.comp_assoc]
      _ = e.forward.comp
          ((f.forward.comp f.inverse).comp e.inverse) := by
        rw [PointedMapGerm.comp_assoc]
      _ = e.forward.comp e.inverse := by
        rw [f.forward_inverse, PointedMapGerm.identity_comp]
      _ = PointedMapGerm.identity n := e.forward_inverse
  inverse_forward := by
    calc
      (f.inverse.comp e.inverse).comp (e.forward.comp f.forward) =
          f.inverse.comp (e.inverse.comp (e.forward.comp f.forward)) := by
        rw [PointedMapGerm.comp_assoc]
      _ = f.inverse.comp
          ((e.inverse.comp e.forward).comp f.forward) := by
        rw [PointedMapGerm.comp_assoc]
      _ = f.inverse.comp f.forward := by
        rw [e.inverse_forward, PointedMapGerm.identity_comp]
      _ = PointedMapGerm.identity n := f.inverse_forward

/-- Pullback by a composite equivalence is the iterated pullback in reverse
order. -/
theorem pullbackAlgEquiv_comp_apply {n : ℕ}
    (e f : PointedEquivGerm n) (q : Germ n) :
    (e.comp f).pullbackAlgEquiv q =
      f.pullbackAlgEquiv (e.pullbackAlgEquiv q) := by
  change (e.forward.comp f.forward).pullbackRingHom q =
    f.forward.pullbackRingHom (e.forward.pullbackRingHom q)
  rw [PointedMapGerm.pullbackRingHom_comp]
  rfl

/-- If an equivalence fixes all germs in the parameter variables, then its
inverse has the same property. -/
theorem symm_pullback_hyperplaneExtension_eq
    {n : ℕ} (e : PointedEquivGerm (n + 1))
    (he : ∀ q : Germ n,
      e.pullbackAlgEquiv (Germ.hyperplaneExtension n q) =
        Germ.hyperplaneExtension n q) (q : Germ n) :
    e.symm.pullbackAlgEquiv (Germ.hyperplaneExtension n q) =
      Germ.hyperplaneExtension n q := by
  have hinverse := e.pullbackRingEquiv.left_inv
    (Germ.hyperplaneExtension n q)
  change e.inverse.pullbackRingHom
      (e.forward.pullbackRingHom (Germ.hyperplaneExtension n q)) =
        Germ.hyperplaneExtension n q at hinverse
  have he' : e.forward.pullbackRingHom
      (Germ.hyperplaneExtension n q) =
        Germ.hyperplaneExtension n q := he q
  rw [he'] at hinverse
  exact hinverse

end PointedEquivGerm

end OnLeConjecture.Analytic

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- An analytic unit multiplying `x²` can be absorbed by a source
coordinate change which leaves the parameter coordinate fixed. -/
theorem exists_parametric_completion_of_square
    (h : Germ 1) (u : Germ 2) (hu : IsUnit u) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin 2) ^ 2 * u +
            Germ.hyperplaneExtension 1 h) =
        Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.hyperplaneExtension 1 h ∧
      (∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
          Germ.hyperplaneExtension 1 q) ∧
      e.forward.1.component (1 : Fin 2) =
        Germ.coordinate (1 : Fin 2) := by
  obtain ⟨v, hv, hvpow⟩ := Germ.exists_isUnit_pow_eq u hu
    (by norm_num : (2 : ℕ) ≠ 0)
  let x : Germ 2 := Germ.coordinate (0 : Fin 2)
  let replacement : Germ 2 := x * v
  have hreplacementMaximal :
      replacement ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [replacement, x]
  have hvValue : Germ.valueRingHom 2 v ≠ 0 :=
    Germ.valueRingHom_ne_zero_of_isUnit hv
  have hreplacementDerivativeValue :
      Germ.valueRingHom 2
          (Germ.partialDerivative (0 : Fin 2) replacement) ≠ 0 := by
    change Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2) (x * v)) ≠ 0
    rw [Germ.partialDerivative_mul,
      Germ.partialDerivative_coordinate_same]
    simpa [x] using hvValue
  have hreplacementRegular :
      Germ.differential replacement (Germ.firstCoordinateVector 1) ≠ 0 := by
    change Germ.differential replacement
      (Germ.coordinateVector (0 : Fin 2)) ≠ 0
    rw [← Germ.valueRingHom_partialDerivative]
    exact hreplacementDerivativeValue
  obtain ⟨c, hcx, hcext⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      replacement hreplacementMaximal hreplacementRegular
  have hcpull :
      c.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.hyperplaneExtension 1 h) =
        Germ.coordinate (0 : Fin 2) ^ 2 * u +
          Germ.hyperplaneExtension 1 h := by
    rw [map_add, map_pow, hcx, hcext h]
    dsimp only [replacement, x]
    rw [mul_pow, hvpow]
  let e := c.symm
  have hparameterCoordinate :
      Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
        Germ.coordinate (1 : Fin 2) := by
    have hi : (0 : Fin 1).succ = (1 : Fin 2) := by decide
    simpa only [hi] using
      Germ.hyperplaneExtension_coordinate (n := 1) (0 : Fin 1)
  refine ⟨e, ?_, ?_, ?_⟩
  · have hinverse := congrArg c.pullbackAlgEquiv.symm hcpull
    rw [c.pullbackAlgEquiv.symm_apply_apply] at hinverse
    exact hinverse.symm
  · intro q
    exact c.symm_pullback_hyperplaneExtension_eq hcext q
  · calc
      e.forward.1.component (1 : Fin 2) =
          e.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) :=
        (e.forward.pullback_coordinate (1 : Fin 2)).symm
      _ = e.pullbackAlgEquiv
          (Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1))) := by
        rw [hparameterCoordinate]
      _ = Germ.hyperplaneExtension 1
          (Germ.coordinate (0 : Fin 1)) := by
        exact c.symm_pullback_hyperplaneExtension_eq hcext _
      _ = Germ.coordinate (1 : Fin 2) := by
        rw [hparameterCoordinate]

/-- Parametric Morse lemma in two variables. If a plane analytic germ
vanishes at the origin, its first derivative in `x` vanishes there, and its
second derivative in `x` does not vanish there, then an analytic source
coordinate change fixes the parameter `y` and transforms the germ into
`x² + h(y)`. -/
theorem exists_parametric_morse_normal_form
    (g : Germ 2) (hg : g ∈ Germ.maximalIdeal 2)
    (hfirst : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2) g) = 0)
    (hsecond : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.partialDerivative (0 : Fin 2) g)) ≠ 0) :
    ∃ (e : PointedEquivGerm 2) (h : Germ 1),
      e.pullbackAlgEquiv g =
        Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.hyperplaneExtension 1 h ∧
      (∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
          Germ.hyperplaneExtension 1 q) ∧
      e.forward.1.component (1 : Fin 2) =
        Germ.coordinate (1 : Fin 2) ∧
      h ∈ Germ.maximalIdeal 1 := by
  let derivative : Germ 2 :=
    Germ.partialDerivative (0 : Fin 2) g
  have hderivativeMaximal :
      derivative ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    exact hfirst
  have hderivativeRegular :
      Germ.differential derivative (Germ.firstCoordinateVector 1) ≠ 0 := by
    change Germ.differential derivative
      (Germ.coordinateVector (0 : Fin 2)) ≠ 0
    rw [← Germ.valueRingHom_partialDerivative]
    exact hsecond
  obtain ⟨c, hcDerivative, hcExtension⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      derivative hderivativeMaximal hderivativeRegular
  let s : PointedEquivGerm 2 := c.symm
  have hsExtension (q : Germ 1) :
      s.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
        Germ.hyperplaneExtension 1 q :=
    c.symm_pullback_hyperplaneExtension_eq hcExtension q
  have hparameterCoordinate :
      Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
        Germ.coordinate (1 : Fin 2) := by
    have hi : (0 : Fin 1).succ = (1 : Fin 2) := by decide
    simpa only [hi] using
      Germ.hyperplaneExtension_coordinate (n := 1) (0 : Fin 1)
  have hsParameter :
      s.forward.1.component (1 : Fin 2) =
        Germ.coordinate (1 : Fin 2) := by
    calc
      s.forward.1.component (1 : Fin 2) =
          s.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) :=
        (s.forward.pullback_coordinate (1 : Fin 2)).symm
      _ = s.pullbackAlgEquiv
          (Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1))) := by
        rw [hparameterCoordinate]
      _ = Germ.hyperplaneExtension 1
          (Germ.coordinate (0 : Fin 1)) := hsExtension _
      _ = Germ.coordinate (1 : Fin 2) := hparameterCoordinate
  have hsDerivative :
      s.pullbackAlgEquiv derivative =
        Germ.coordinate (0 : Fin 2) := by
    have hinverse := c.pullbackRingEquiv.left_inv
      (Germ.coordinate (0 : Fin 2))
    change c.inverse.pullbackRingHom
        (c.forward.pullbackRingHom (Germ.coordinate (0 : Fin 2))) =
      Germ.coordinate (0 : Fin 2) at hinverse
    have hcDerivative' : c.forward.pullbackRingHom
        (Germ.coordinate (0 : Fin 2)) = derivative := hcDerivative
    rw [hcDerivative'] at hinverse
    exact hinverse
  let transformed : Germ 2 := s.pullbackAlgEquiv g
  let coefficient : Germ 2 := Germ.partialDerivative (0 : Fin 2)
    (s.forward.1.component (0 : Fin 2))
  have htransformedDerivative :
      Germ.partialDerivative (0 : Fin 2) transformed =
        Germ.coordinate (0 : Fin 2) * coefficient := by
    change Germ.partialDerivative (0 : Fin 2)
        (Germ.compPointed g s.forward) =
      Germ.coordinate (0 : Fin 2) *
        Germ.partialDerivative (0 : Fin 2)
          (s.forward.1.component (0 : Fin 2))
    rw [Germ.partialDerivative_compPointed]
    have hsDerivative' : Germ.compPointed derivative s.forward =
        Germ.coordinate (0 : Fin 2) := hsDerivative
    rw [hsDerivative', hsParameter,
      Germ.partialDerivative_coordinate_ne (by decide)]
    ring
  have hcoordinateJacobian :
      Germ.coordinateJacobian s.forward = coefficient := by
    rw [Germ.coordinateJacobian_eq, hsParameter,
      Germ.partialDerivative_coordinate_same,
      Germ.partialDerivative_coordinate_ne (by decide)]
    dsimp only [coefficient]
    ring
  have hcoefficientUnit : IsUnit coefficient := by
    rw [← hcoordinateJacobian]
    exact Germ.PointedEquivGerm.coordinateJacobian_isUnit s
  let h : Germ 1 := Germ.hyperplaneRestriction 1 transformed
  have hrestrictionExtension :
      Germ.hyperplaneRestriction 1 (Germ.hyperplaneExtension 1 h) = h := by
    simpa using DFunLike.congr_fun
      (Germ.hyperplaneRestriction_comp_extension 1) h
  have hdifference :
      transformed - Germ.hyperplaneExtension 1 h ∈
        RingHom.ker (Germ.hyperplaneRestriction 1) := by
    rw [RingHom.mem_ker, map_sub, hrestrictionExtension]
    simp [h]
  rw [Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero,
    Ideal.mem_span_singleton] at hdifference
  rcases hdifference with ⟨r, hr⟩
  have htransformedFactor :
      transformed = Germ.coordinate (0 : Fin 2) * r +
        Germ.hyperplaneExtension 1 h := by
    exact sub_eq_iff_eq_add.mp hr
  have htransformedDerivativeFactor :
      Germ.partialDerivative (0 : Fin 2) transformed =
        r + Germ.coordinate (0 : Fin 2) *
          Germ.partialDerivative (0 : Fin 2) r := by
    rw [htransformedFactor, Germ.partialDerivative_add,
      Germ.partialDerivative_mul,
      Germ.partialDerivative_coordinate_same,
      Germ.partialDerivative_zero_hyperplaneExtension]
    ring
  have hcoefficientIdentity :
      Germ.coordinate (0 : Fin 2) * coefficient =
        r + Germ.coordinate (0 : Fin 2) *
          Germ.partialDerivative (0 : Fin 2) r :=
    htransformedDerivative.symm.trans htransformedDerivativeFactor
  have hrRestriction : Germ.hyperplaneRestriction 1 r = 0 := by
    have hrestricted := congrArg (Germ.hyperplaneRestriction 1)
      hcoefficientIdentity
    simp only [map_add, map_mul,
      Germ.hyperplaneRestriction_coordinate_zero,
      zero_mul] at hrestricted
    simpa only [add_zero] using hrestricted.symm
  have hrKernel : r ∈ RingHom.ker (Germ.hyperplaneRestriction 1) := by
    rw [RingHom.mem_ker]
    exact hrRestriction
  rw [Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero,
    Ideal.mem_span_singleton] at hrKernel
  rcases hrKernel with ⟨u, hu⟩
  have hrFactor : r = Germ.coordinate (0 : Fin 2) * u := hu
  have hcancelIdentity : coefficient =
      (2 : Germ 2) * u + Germ.coordinate (0 : Fin 2) *
        Germ.partialDerivative (0 : Fin 2) u := by
    apply mul_left_cancel₀ (Germ.coordinate_ne_zero (0 : Fin 2))
    calc
      Germ.coordinate (0 : Fin 2) * coefficient =
          r + Germ.coordinate (0 : Fin 2) *
            Germ.partialDerivative (0 : Fin 2) r := hcoefficientIdentity
      _ = Germ.coordinate (0 : Fin 2) *
          ((2 : Germ 2) * u + Germ.coordinate (0 : Fin 2) *
            Germ.partialDerivative (0 : Fin 2) u) := by
        rw [hrFactor, Germ.partialDerivative_mul,
          Germ.partialDerivative_coordinate_same]
        ring
  have huUnit : IsUnit u := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    intro huValue
    have hcoefficientValue : Germ.valueRingHom 2 coefficient ≠ 0 :=
      Germ.valueRingHom_ne_zero_of_isUnit hcoefficientUnit
    apply hcoefficientValue
    rw [hcancelIdentity]
    simp [huValue]
  have htransformedQuadratic : transformed =
      Germ.coordinate (0 : Fin 2) ^ 2 * u +
        Germ.hyperplaneExtension 1 h := by
    rw [htransformedFactor, hrFactor]
    ring
  obtain ⟨d, hdNormal, hdExtension, hdParameter⟩ :=
    exists_parametric_completion_of_square h u huUnit
  let e : PointedEquivGerm 2 := s.comp d
  have heNormal : e.pullbackAlgEquiv g =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.hyperplaneExtension 1 h := by
    change (s.comp d).pullbackAlgEquiv g = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change d.pullbackAlgEquiv transformed = _
    rw [htransformedQuadratic]
    exact hdNormal
  have heExtension (q : Germ 1) :
      e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
        Germ.hyperplaneExtension 1 q := by
    change (s.comp d).pullbackAlgEquiv
      (Germ.hyperplaneExtension 1 q) = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply,
      hsExtension q, hdExtension q]
  have heParameter : e.forward.1.component (1 : Fin 2) =
      Germ.coordinate (1 : Fin 2) := by
    calc
      e.forward.1.component (1 : Fin 2) =
          e.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) :=
        (e.forward.pullback_coordinate (1 : Fin 2)).symm
      _ = e.pullbackAlgEquiv
          (Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1))) := by
        rw [hparameterCoordinate]
      _ = Germ.hyperplaneExtension 1
          (Germ.coordinate (0 : Fin 1)) := heExtension _
      _ = Germ.coordinate (1 : Fin 2) := hparameterCoordinate
  have htransformedMaximal : transformed ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    change Germ.valueRingHom 2 (s.forward.pullbackRingHom g) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact Germ.mem_maximalIdeal_iff.mp hg
  have hhMaximal : h ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    change Germ.valueRingHom 1
      ((Germ.hyperplaneInclusionGerm 1).pullbackRingHom transformed) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact Germ.mem_maximalIdeal_iff.mp htransformedMaximal
  exact ⟨e, h, heNormal, heExtension, heParameter, hhMaximal⟩

/-- The parametric Morse normal form stated using the maximal ideal and unit
conditions on the first two `x` derivatives. -/
theorem exists_parametric_morse_normal_form_of_derivative_mem_and_isUnit
    (g : Germ 2) (hg : g ∈ Germ.maximalIdeal 2)
    (hfirst : Germ.partialDerivative (0 : Fin 2) g ∈
      Germ.maximalIdeal 2)
    (hsecond : IsUnit
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.partialDerivative (0 : Fin 2) g))) :
    ∃ (e : PointedEquivGerm 2) (h : Germ 1),
      e.pullbackAlgEquiv g =
        Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.hyperplaneExtension 1 h ∧
      (∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
          Germ.hyperplaneExtension 1 q) ∧
      e.forward.1.component (1 : Fin 2) =
        Germ.coordinate (1 : Fin 2) ∧
      h ∈ Germ.maximalIdeal 1 := by
  apply exists_parametric_morse_normal_form g hg
  · exact Germ.mem_maximalIdeal_iff.mp hfirst
  · exact Germ.valueRingHom_ne_zero_of_isUnit hsecond

end OnLeConjecture.PlaneCurve
