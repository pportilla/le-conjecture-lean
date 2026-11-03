/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Hyperplane
public import OnLeConjecture.Analytic.Dimension
public import OnLeConjecture.Analytic.PullbackEquivalence
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Quadratic decomposition of plane analytic germs

This file isolates the analytic algebra behind the decomposition with respect
to the first coordinate. Reflection in that coordinate splits every plane
analytic germ into an invariant summand and the first coordinate times another
invariant summand. It also constructs pullback by `(u, y) = (x^2, y)` and
proves its injectivity. The remaining descent assertion is stated explicitly:
an invariant analytic germ must be the pullback of an analytic germ in
`(u, y)`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Reflection in the first coordinate of `Source 2`. -/
@[expose] noncomputable def firstCoordinateReflection :
    Source 2 →L[ℂ] Source 2 :=
  ContinuousLinearMap.pi fun i ↦
    Fin.cases
      (-(ContinuousLinearMap.proj (R := ℂ)
        (0 : Fin 2)))
      (fun j ↦ ContinuousLinearMap.proj (R := ℂ) j.succ) i

@[simp]
theorem firstCoordinateReflection_apply_zero (z : Source 2) :
    firstCoordinateReflection z 0 = -z 0 := by
  simp [firstCoordinateReflection]

@[simp]
theorem firstCoordinateReflection_apply_one (z : Source 2) :
    firstCoordinateReflection z 1 = z 1 := by
  change
    Fin.cases (-z 0) (fun j : Fin 1 ↦ z j.succ) 1 = z 1
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rfl

@[simp]
theorem firstCoordinateReflection_zero :
    firstCoordinateReflection (0 : Source 2) = 0 := by
  exact map_zero firstCoordinateReflection

@[simp]
theorem firstCoordinateReflection_involutive (z : Source 2) :
    firstCoordinateReflection (firstCoordinateReflection z) = z := by
  ext i
  fin_cases i
  · simp
  · simp

/-- Reflection in the first coordinate as a pointed analytic germ. -/
@[expose] noncomputable def firstCoordinateReflectionGerm :
    PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction firstCoordinateReflection
    (firstCoordinateReflection.analyticAt 0)
    firstCoordinateReflection_zero

@[simp]
theorem firstCoordinateReflectionGerm_comp_self :
    firstCoordinateReflectionGerm.comp firstCoordinateReflectionGerm =
      PointedMapGerm.identity 2 := by
  rw [firstCoordinateReflectionGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    firstCoordinateReflection_involutive z

/-- Reflection in the first coordinate as an invertible analytic germ. -/
@[expose] noncomputable def firstCoordinateReflectionEquiv :
    PointedEquivGerm 2 where
  forward := firstCoordinateReflectionGerm
  inverse := firstCoordinateReflectionGerm
  forward_inverse := firstCoordinateReflectionGerm_comp_self
  inverse_forward := firstCoordinateReflectionGerm_comp_self

/-- Pullback by reflection in the first coordinate. -/
@[expose] noncomputable def reflectionAlgEquiv :
    Germ 2 ≃ₐ[ℂ] Germ 2 :=
  firstCoordinateReflectionEquiv.pullbackAlgEquiv

@[simp]
theorem reflectionAlgEquiv_apply_apply (f : Germ 2) :
    reflectionAlgEquiv (reflectionAlgEquiv f) = f := by
  exact reflectionAlgEquiv.symm_apply_apply f

@[simp]
theorem reflectionAlgEquiv_coordinate_zero :
    reflectionAlgEquiv (Germ.coordinate (0 : Fin 2)) =
      -Germ.coordinate (0 : Fin 2) := by
  rw [reflectionAlgEquiv, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem reflectionAlgEquiv_coordinate_one :
    reflectionAlgEquiv (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [reflectionAlgEquiv, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

/-- The analytic map `(x, y) ↦ (x^2, y)`. -/
@[expose] noncomputable def quadraticMap (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 ^ 2) (fun j ↦ z j.succ) i

@[simp]
theorem quadraticMap_apply_zero (z : Source 2) :
    quadraticMap z 0 = z 0 ^ 2 := by
  simp [quadraticMap]

@[simp]
theorem quadraticMap_apply_one (z : Source 2) :
    quadraticMap z 1 = z 1 := by
  change Fin.cases (z 0 ^ 2) (fun j : Fin 1 ↦ z j.succ) 1 = z 1
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rfl

theorem quadraticMap_analyticAt :
    AnalyticAt ℂ quadraticMap 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).pow 2
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

@[simp]
theorem quadraticMap_zero : quadraticMap (0 : Source 2) = 0 := by
  ext i
  fin_cases i
  · simp
  · simp

/-- The pointed analytic germ represented by `(x, y) ↦ (x^2, y)`. -/
@[expose] noncomputable def quadraticMapGerm : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction quadraticMap quadraticMap_analyticAt quadraticMap_zero

/-- Substitution `(u, y) = (x^2, y)` on plane analytic germs. -/
@[expose] noncomputable def quadraticSubstitutionAlgHom :
    Germ 2 →ₐ[ℂ] Germ 2 where
  __ := quadraticMapGerm.pullbackRingHom
  commutes' c := quadraticMapGerm.pullback_constRingHom c

@[simp]
theorem quadraticSubstitutionAlgHom_coordinate_zero :
    quadraticSubstitutionAlgHom (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) ^ 2 := by
  change quadraticMapGerm.pullbackRingHom
      (Germ.coordinate (0 : Fin 2)) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem quadraticSubstitutionAlgHom_coordinate_one :
    quadraticSubstitutionAlgHom (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  change quadraticMapGerm.pullbackRingHom
      (Germ.coordinate (1 : Fin 2)) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

/-- Pullback by `(x, y) ↦ (x^2, y)` is fixed by reflection. -/
theorem reflection_quadraticSubstitution (f : Germ 2) :
    reflectionAlgEquiv (quadraticSubstitutionAlgHom f) =
      quadraticSubstitutionAlgHom f := by
  rcases f with ⟨f, hf⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by
        change f (quadraticMap (firstCoordinateReflection z)) =
          f (quadraticMap z)
        congr 1
        ext i
        fin_cases i
        · simp [quadraticMap]
        · change firstCoordinateReflection z 1 = z 1
          exact firstCoordinateReflection_apply_one z

/-- A neighborhood on which two functions agree after the quadratic map
determines a neighborhood on which the original functions agree. -/
theorem eventuallyEq_of_comp_quadraticMap {f g : Source 2 → ℂ}
    (hfg : (f ∘ quadraticMap) =ᶠ[nhds 0] (g ∘ quadraticMap)) :
    f =ᶠ[nhds 0] g := by
  rcases Metric.eventually_nhds_iff.mp hfg with ⟨ε, hε, hball⟩
  let δ : ℝ := min ε (ε ^ 2)
  have hδ : 0 < δ := lt_min hε (pow_pos hε 2)
  have hδε : δ ≤ ε := min_le_left ε (ε ^ 2)
  have hδsq : δ ≤ ε ^ 2 := min_le_right ε (ε ^ 2)
  apply Filter.Eventually.mono (Metric.ball_mem_nhds (0 : Source 2) hδ)
  intro z hz
  have hzNorm : ‖z‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzCoord : ∀ i, ‖z i‖ < δ :=
    (@pi_norm_lt_iff (Fin 2) (fun _ : Fin 2 ↦ ℂ) inferInstance
      (fun _ ↦ inferInstance) z δ hδ).mp hzNorm
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (z 0) zero_lt_two
  let w : Source 2 := fun i ↦
    Fin.cases x (fun j : Fin 1 ↦ z j.succ) i
  have hwZero : w 0 = x := by simp [w]
  have hwOne : w 1 = z 1 := by
    change Fin.cases x (fun j : Fin 1 ↦ z j.succ) 1 = z 1
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
    rfl
  have hxNormPow : ‖x‖ ^ 2 = ‖z 0‖ := by
    calc
      ‖x‖ ^ 2 = ‖x ^ 2‖ := (norm_pow x 2).symm
      _ = ‖z 0‖ := by rw [hx]
  have hxNormLt : ‖x‖ < ε := by
    have hxSqLt : ‖x‖ ^ 2 < ε ^ 2 := by
      rw [hxNormPow]
      exact (hzCoord 0).trans_le hδsq
    nlinarith [norm_nonneg x]
  have hwNorm : ‖w‖ < ε := by
    apply (@pi_norm_lt_iff (Fin 2) (fun _ : Fin 2 ↦ ℂ) inferInstance
      (fun _ ↦ inferInstance) w ε hε).mpr
    intro i
    induction i using Fin.cases with
    | zero =>
        change ‖w 0‖ < ε
        rw [hwZero]
        exact hxNormLt
    | succ j =>
        fin_cases j
        change ‖w 1‖ < ε
        rw [hwOne]
        exact (hzCoord 1).trans_le hδε
  have hwBall : w ∈ Metric.ball (0 : Source 2) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hwNorm
  have hquadratic : quadraticMap w = z := by
    ext i
    induction i using Fin.cases with
    | zero =>
        change w 0 ^ 2 = z 0
        rw [hwZero, hx]
    | succ j =>
        fin_cases j
        change w 1 = z 1
        exact hwOne
  have heq := hball hwBall
  simpa only [Function.comp_apply, hquadratic] using heq

/-- Substitution `(u, y) = (x^2, y)` is injective on analytic germs. -/
theorem quadraticSubstitutionAlgHom_injective :
    Function.Injective quadraticSubstitutionAlgHom := by
  intro f g hfg
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  change IsAnalyticGerm f at hf
  change IsAnalyticGerm g at hg
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          rw [isAnalyticGerm_ofFun] at hf hg
          change Germ.compPointed (Germ.ofFunction f hf) quadraticMapGerm =
            Germ.compPointed (Germ.ofFunction g hg) quadraticMapGerm at hfg
          rw [quadraticMapGerm, Germ.compPointed_ofFunction,
            Germ.compPointed_ofFunction] at hfg
          apply Subtype.ext
          apply Filter.Germ.coe_eq.mpr
          apply eventuallyEq_of_comp_quadraticMap
          apply Filter.Germ.coe_eq.mp
          exact congrArg Subtype.val hfg

/-- The part of a germ fixed by reflection. -/
@[expose] noncomputable def invariantPart (f : Germ 2) : Germ 2 :=
  (1 / 2 : ℂ) • (f + reflectionAlgEquiv f)

/-- The part of a germ negated by reflection. -/
@[expose] noncomputable def antiInvariantPart (f : Germ 2) : Germ 2 :=
  (1 / 2 : ℂ) • (f - reflectionAlgEquiv f)

@[simp]
theorem reflection_invariantPart (f : Germ 2) :
    reflectionAlgEquiv (invariantPart f) = invariantPart f := by
  simp only [invariantPart, map_smul, map_add,
    reflectionAlgEquiv_apply_apply]
  rw [add_comm]

@[simp]
theorem reflection_antiInvariantPart (f : Germ 2) :
    reflectionAlgEquiv (antiInvariantPart f) = -antiInvariantPart f := by
  simp only [antiInvariantPart, map_smul, map_sub,
    reflectionAlgEquiv_apply_apply]
  module

/-- A germ is the sum of its invariant and anti invariant parts. -/
theorem invariantPart_add_antiInvariantPart (f : Germ 2) :
    invariantPart f + antiInvariantPart f = f := by
  simp only [invariantPart, antiInvariantPart]
  module

/-- Reflection followed by inclusion of the coordinate hyperplane equals
the inclusion. -/
theorem firstCoordinateReflectionGerm_comp_hyperplaneInclusion :
    firstCoordinateReflectionGerm.comp (hyperplaneInclusionGerm 1) =
      hyperplaneInclusionGerm 1 := by
  rw [firstCoordinateReflectionGerm, hyperplaneInclusionGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        fin_cases j
        simp

/-- Restriction to `x = 0` is unchanged by reflection. -/
theorem hyperplaneRestriction_reflection (f : Germ 2) :
    hyperplaneRestriction 1 (reflectionAlgEquiv f) =
      hyperplaneRestriction 1 f := by
  change (hyperplaneInclusionGerm 1).pullbackRingHom
      (firstCoordinateReflectionGerm.pullbackRingHom f) =
    (hyperplaneInclusionGerm 1).pullbackRingHom f
  have hcomp := DFunLike.congr_fun
    (PointedMapGerm.pullbackRingHom_comp
      firstCoordinateReflectionGerm (hyperplaneInclusionGerm 1)) f
  rw [firstCoordinateReflectionGerm_comp_hyperplaneInclusion] at hcomp
  exact hcomp.symm

/-- An anti invariant germ restricts to zero on `x = 0`. -/
theorem hyperplaneRestriction_eq_zero_of_reflection_eq_neg
    {f : Germ 2} (hf : reflectionAlgEquiv f = -f) :
    hyperplaneRestriction 1 f = 0 := by
  have hreflect :
      hyperplaneRestriction 1 (reflectionAlgEquiv f) =
        hyperplaneRestriction 1 f :=
    hyperplaneRestriction_reflection f
  rw [hf, map_neg] at hreflect
  let r := hyperplaneRestriction 1 f
  have hr : r + r = 0 := by
    calc
      r + r = -r + r := congrArg (fun q : Germ 1 ↦ q + r) hreflect.symm
      _ = 0 := neg_add_cancel r
  calc
    hyperplaneRestriction 1 f = (1 / 2 : ℂ) • (r + r) := by
      dsimp [r]
      module
    _ = 0 := by rw [hr, smul_zero]

/-- Every anti invariant germ is the first coordinate times a unique invariant
germ. -/
theorem existsUnique_coordinate_mul_invariant_of_reflection_eq_neg
    {f : Germ 2} (hf : reflectionAlgEquiv f = -f) :
    ∃! c : Germ 2,
      f = Germ.coordinate (0 : Fin 2) * c ∧
        reflectionAlgEquiv c = c := by
  have hrestriction : hyperplaneRestriction 1 f = 0 :=
    hyperplaneRestriction_eq_zero_of_reflection_eq_neg hf
  have hmem : f ∈ RingHom.ker (hyperplaneRestriction 1) := by
    rw [RingHom.mem_ker]
    exact hrestriction
  rw [ker_hyperplaneRestriction_eq_span_coordinate_zero] at hmem
  rw [Ideal.mem_span_singleton'] at hmem
  rcases hmem with ⟨c, hc⟩
  have hfactor : f = Germ.coordinate (0 : Fin 2) * c := by
    rw [← hc, mul_comm]
  have hmul :
      Germ.coordinate (0 : Fin 2) * c =
        Germ.coordinate (0 : Fin 2) * reflectionAlgEquiv c := by
    calc
      Germ.coordinate (0 : Fin 2) * c = f := hfactor.symm
      _ = -reflectionAlgEquiv f := by
        rw [hf]
        simp
      _ = -reflectionAlgEquiv
          (Germ.coordinate (0 : Fin 2) * c) := by rw [← hfactor]
      _ = Germ.coordinate (0 : Fin 2) * reflectionAlgEquiv c := by
        rw [map_mul, reflectionAlgEquiv_coordinate_zero]
        ring
  have hinvariant : reflectionAlgEquiv c = c := by
    symm
    exact mul_left_cancel₀ (Germ.coordinate_ne_zero (0 : Fin 2)) hmul
  refine ⟨c, ⟨hfactor, hinvariant⟩, ?_⟩
  intro d hd
  apply mul_left_cancel₀ (Germ.coordinate_ne_zero (0 : Fin 2))
  rw [← hfactor, hd.1]

/-- The invariant projection of an invariant germ plus the first coordinate
times an invariant germ is the first summand. -/
theorem invariantPart_add_coordinate_mul_of_invariant
    {a b : Germ 2} (ha : reflectionAlgEquiv a = a)
    (hb : reflectionAlgEquiv b = b) :
    invariantPart (a + Germ.coordinate (0 : Fin 2) * b) = a := by
  simp only [invariantPart, map_add, map_mul, ha, hb,
    reflectionAlgEquiv_coordinate_zero]
  have hinside :
      a + Germ.coordinate (0 : Fin 2) * b +
          (a + -Germ.coordinate (0 : Fin 2) * b) = a + a := by
    ring
  rw [hinside, smul_add, ← add_smul]
  norm_num

/-- The anti invariant projection of an invariant germ plus the first
coordinate times an invariant germ is the second summand multiplied by that
coordinate. -/
theorem antiInvariantPart_add_coordinate_mul_of_invariant
    {a b : Germ 2} (ha : reflectionAlgEquiv a = a)
    (hb : reflectionAlgEquiv b = b) :
    antiInvariantPart (a + Germ.coordinate (0 : Fin 2) * b) =
      Germ.coordinate (0 : Fin 2) * b := by
  simp only [antiInvariantPart, map_add, map_mul, ha, hb,
    reflectionAlgEquiv_coordinate_zero]
  have hinside :
      a + Germ.coordinate (0 : Fin 2) * b -
          (a + -Germ.coordinate (0 : Fin 2) * b) =
        Germ.coordinate (0 : Fin 2) * b +
          Germ.coordinate (0 : Fin 2) * b := by
    ring
  rw [hinside, smul_add, ← add_smul]
  norm_num

/-- Every plane analytic germ has a unique decomposition into an invariant
germ plus the first coordinate times an invariant germ. -/
theorem existsUnique_invariant_add_coordinate_mul_invariant (f : Germ 2) :
    ∃! p : Germ 2 × Germ 2,
      f = p.1 + Germ.coordinate (0 : Fin 2) * p.2 ∧
        reflectionAlgEquiv p.1 = p.1 ∧
          reflectionAlgEquiv p.2 = p.2 := by
  rcases existsUnique_coordinate_mul_invariant_of_reflection_eq_neg
      (reflection_antiInvariantPart f) with ⟨c, hc, hcUnique⟩
  refine ⟨⟨invariantPart f, c⟩, ?_, ?_⟩
  · refine ⟨?_, reflection_invariantPart f, hc.2⟩
    calc
      f = invariantPart f + antiInvariantPart f :=
        (invariantPart_add_antiInvariantPart f).symm
      _ = invariantPart f + Germ.coordinate (0 : Fin 2) * c := by
        rw [hc.1]
  · intro p hp
    rcases p with ⟨a, b⟩
    apply Prod.ext
    · change a = invariantPart f
      rw [hp.1,
        invariantPart_add_coordinate_mul_of_invariant hp.2.1 hp.2.2]
    · apply hcUnique b
      refine ⟨?_, hp.2.2⟩
      rw [hp.1,
        antiInvariantPart_add_coordinate_mul_of_invariant hp.2.1 hp.2.2]

/-- An invariant germ equals its invariant projection. -/
theorem invariantPart_eq_self_of_reflection_eq {f : Germ 2}
    (hf : reflectionAlgEquiv f = f) : invariantPart f = f := by
  rw [invariantPart, hf, smul_add, ← add_smul]
  norm_num

/-- The analytic descent assertion for the quadratic quotient map. -/
@[expose] def QuadraticInvariantDescent : Prop :=
  ∀ f : Germ 2, reflectionAlgEquiv f = f →
    ∃ a : Germ 2, quadraticSubstitutionAlgHom a = f

/-- Once invariant germs descend through `(x, y) ↦ (x^2, y)`, every germ
has a quadratic decomposition. -/
theorem exists_quadratic_decomposition_of_invariantDescent
    (hdescent : QuadraticInvariantDescent) (f : Germ 2) :
    ∃ a b : Germ 2,
      f = quadraticSubstitutionAlgHom a +
        Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b := by
  rcases existsUnique_invariant_add_coordinate_mul_invariant f with
    ⟨p, hp, _hpUnique⟩
  rcases hdescent p.1 hp.2.1 with ⟨a, ha⟩
  rcases hdescent p.2 hp.2.2 with ⟨b, hb⟩
  refine ⟨a, b, ?_⟩
  calc
    f = p.1 + Germ.coordinate (0 : Fin 2) * p.2 := hp.1
    _ = quadraticSubstitutionAlgHom a +
        Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b := by
      rw [ha, hb]

/-- The coefficients in a quadratic decomposition are unique. -/
theorem quadratic_decomposition_unique
    {f a b a' b' : Germ 2}
    (h : f = quadraticSubstitutionAlgHom a +
      Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b)
    (h' : f = quadraticSubstitutionAlgHom a' +
      Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b') :
    a = a' ∧ b = b' := by
  have haInvariant :
      reflectionAlgEquiv (quadraticSubstitutionAlgHom a) =
        quadraticSubstitutionAlgHom a :=
    reflection_quadraticSubstitution a
  have hbInvariant :
      reflectionAlgEquiv (quadraticSubstitutionAlgHom b) =
        quadraticSubstitutionAlgHom b :=
    reflection_quadraticSubstitution b
  have haInvariant' :
      reflectionAlgEquiv (quadraticSubstitutionAlgHom a') =
        quadraticSubstitutionAlgHom a' :=
    reflection_quadraticSubstitution a'
  have hbInvariant' :
      reflectionAlgEquiv (quadraticSubstitutionAlgHom b') =
        quadraticSubstitutionAlgHom b' :=
    reflection_quadraticSubstitution b'
  have haImage : invariantPart f = quadraticSubstitutionAlgHom a := by
    rw [h]
    exact invariantPart_add_coordinate_mul_of_invariant
      haInvariant hbInvariant
  have haImage' : invariantPart f = quadraticSubstitutionAlgHom a' := by
    rw [h']
    exact invariantPart_add_coordinate_mul_of_invariant
      haInvariant' hbInvariant'
  have hbImage :
      antiInvariantPart f =
        Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b := by
    rw [h]
    exact antiInvariantPart_add_coordinate_mul_of_invariant
      haInvariant hbInvariant
  have hbImage' :
      antiInvariantPart f =
        Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b' := by
    rw [h']
    exact antiInvariantPart_add_coordinate_mul_of_invariant
      haInvariant' hbInvariant'
  constructor
  · apply quadraticSubstitutionAlgHom_injective
    exact haImage.symm.trans haImage'
  · apply quadraticSubstitutionAlgHom_injective
    apply mul_left_cancel₀ (Germ.coordinate_ne_zero (0 : Fin 2))
    exact hbImage.symm.trans hbImage'

/-- Quadratic invariant descent is equivalent to existence of quadratic
decompositions for all plane analytic germs. -/
theorem quadraticInvariantDescent_iff_forall_exists_decomposition :
    QuadraticInvariantDescent ↔
      ∀ f : Germ 2, ∃ a b : Germ 2,
        f = quadraticSubstitutionAlgHom a +
          Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom b := by
  constructor
  · exact exists_quadratic_decomposition_of_invariantDescent
  · intro hdecomposition f hf
    rcases hdecomposition f with ⟨a, b, hab⟩
    refine ⟨a, ?_⟩
    calc
      quadraticSubstitutionAlgHom a = invariantPart f := by
        rw [hab]
        symm
        exact invariantPart_add_coordinate_mul_of_invariant
          (reflection_quadraticSubstitution a)
          (reflection_quadraticSubstitution b)
      _ = f := invariantPart_eq_self_of_reflection_eq hf

/-- Under quadratic invariant descent, every plane analytic germ has a unique
expression `A(x^2, y) + x B(x^2, y)`. -/
theorem existsUnique_quadratic_decomposition
    (hdescent : QuadraticInvariantDescent) (f : Germ 2) :
    ∃! p : Germ 2 × Germ 2,
      f = quadraticSubstitutionAlgHom p.1 +
        Germ.coordinate (0 : Fin 2) * quadraticSubstitutionAlgHom p.2 := by
  rcases exists_quadratic_decomposition_of_invariantDescent hdescent f with
    ⟨a, b, hab⟩
  refine ⟨⟨a, b⟩, hab, ?_⟩
  intro p hp
  rcases p with ⟨a', b'⟩
  rcases quadratic_decomposition_unique hp hab with ⟨ha, hb⟩
  exact Prod.ext ha hb

end Germ

end OnLeConjecture.Analytic
