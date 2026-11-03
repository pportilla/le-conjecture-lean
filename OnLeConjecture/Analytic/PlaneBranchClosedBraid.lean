/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitRoot
public import OnLeConjecture.Analytic.InjectiveCurveMultiplicity
public import OnLeConjecture.Analytic.CurveInitialFactor
public import OnLeConjecture.Analytic.ResolutionSectionAssembly
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.FiniteDimensional

/-!
# Closed-braid projections of injective analytic plane branches

A component of order `a > 0` becomes the power `z^a` after a source
coordinate change. Small parameter circles then embed in the fixed cylinder
`Circle × ℂ`, and the first projection is a covering with exactly `a` points
in every fibre. The circle is constructed from a representative of the given
analytic germ. Positivity, braid-word realization, and identification with
the small-sphere link are not asserted here.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- Positive powers preserve the unit circle exactly. -/
theorem norm_pow_eq_one_iff {a : ℕ} (ha : 0 < a) (z : ℂ) :
    ‖z ^ a‖ = 1 ↔ ‖z‖ = 1 := by
  rw [norm_pow]
  simpa only [one_pow] using pow_left_inj₀ (norm_nonneg z) zero_le_one ha.ne'

/-- The power projection of the circle is a covering map. -/
theorem circle_pow_isCoveringMap {a : ℕ} (ha : 0 < a) :
    IsCoveringMap (fun u : Circle => u ^ a) := by
  have hcover : IsCoveringMapOn (fun z : ℂ => z ^ a) (sphere 0 1) :=
    (isCoveringMapOn_npow a (show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne')).mono
      (fun z hz => by
        change z ≠ 0
        intro h
        simp [h] at hz)
  have heq : sphere (0 : ℂ) 1 = (fun z : ℂ => z ^ a) ⁻¹' sphere 0 1 := by
    ext z
    simp only [mem_preimage, mem_sphere_zero_iff_norm, norm_pow_eq_one_iff ha]
  exact hcover.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr heq)

/-- Every point of the unit circle has an `a`th root on that circle. -/
theorem circle_pow_surjective {a : ℕ} (ha : 0 < a) :
    Function.Surjective (fun u : Circle => u ^ a) := by
  intro v
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (v : ℂ) ha
  have hn : ‖z‖ = 1 := (norm_pow_eq_one_iff ha z).mp (by rw [hz, Circle.norm_coe])
  exact ⟨⟨z, mem_sphere_zero_iff_norm.mpr hn⟩, Circle.ext hz⟩

/-- The kernel of a power on the circle is exactly the complex roots of unity. -/
def circlePowKernelEquivRoots {a : ℕ} (ha : 0 < a) :
    (powMonoidHom (α := Circle) a).ker ≃ rootsOfUnity a ℂ where
  toFun u := ⟨Circle.toUnits u, by
    apply Units.ext
    exact congrArg (fun v : Circle => (v : ℂ)) u.property⟩
  invFun u := ⟨⟨(u.val : ℂ), mem_sphere_zero_iff_norm.mpr
    ((norm_pow_eq_one_iff ha _).mp (by
      have hu : (u.val : ℂ) ^ a = 1 :=
        congrArg (fun v : ℂˣ => (v : ℂ)) u.property
      rw [hu, norm_one]))⟩,
    Circle.ext (congrArg (fun v : ℂˣ => (v : ℂ)) u.property)⟩
  left_inv u := by rfl
  right_inv u := by apply Subtype.ext; apply Units.ext; rfl

/-- Each fibre of the circle power projection has precisely `a` elements. -/
theorem circle_pow_fiber_card {a : ℕ} (ha : 0 < a) (v : Circle) :
    Nat.card {u : Circle // u ^ a = v} = a := by
  let : NeZero a := ⟨ha.ne'⟩
  let e := MonoidHom.fiberEquivKerOfSurjective
    (f := powMonoidHom (α := Circle) a) (circle_pow_surjective ha) v
  exact (Nat.card_congr (e.trans (circlePowKernelEquivRoots ha))).trans
    (Complex.card_rootsOfUnity a)

/-- A prescribed finite positive component order is the exponent in a source
coordinate normalization, with no change of the target coordinates. -/
theorem PointedMapGerm.exists_source_equiv_component_power
    (β : PointedMapGerm 1 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a) :
    ∃ e : PointedEquivGerm 1,
      (β.comp e.inverse).1.component i = Germ.coordinate 0 ^ a := by
  have hn : β.1.component i ≠ 0 := by
    intro h
    simp only [h, Germ.vanishingOrder_zero] at ho
    exact ENat.top_ne_natCast a ho
  obtain ⟨k, u, hu, hfactor⟩ := Germ.exists_eq_coordinate_pow_mul_unit hn
  have hk : k = a := ENat.natCast_inj.mp
    ((Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor).symm.trans ho)
  subst k
  obtain ⟨v, hv, hpow⟩ := Germ.exists_isUnit_pow_eq u hu ha.ne'
  obtain ⟨e, he⟩ := Germ.exists_pointedEquivGerm_component_eq_coordinate_mul_unit v hv
  have hepower : e.forward.1.component 0 ^ a = β.1.component i := by
    rw [he, mul_pow, hpow, hfactor]
  refine ⟨e, ?_⟩
  rw [← PointedMapGerm.pullback_coordinate, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply, PointedMapGerm.pullback_coordinate, ← hepower, map_pow]
  have hcancel : e.inverse.pullbackRingHom (e.forward.1.component 0) = Germ.coordinate 0 := by
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (Germ.coordinate 0)) = _
    exact e.pullbackRingEquiv.symm_apply_apply _
  rw [hcancel]

/-- The power normal form holds for an injective analytic representative on
one entire parameter ball. -/
theorem PointedMapGerm.exists_injective_power_representative
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
        AnalyticOnNhd ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
        ∀ z ∈ ball 0 R, F z i = z ^ a := by
  obtain ⟨e, he⟩ := β.exists_source_equiv_component_power i ha ho
  obtain ⟨G, hG, hG0, hg, S, hS, hGi⟩ :=
    β.comp_hasInjectiveRepresentative e.inverse hi e.inverse_hasInjectiveRepresentative
  rw [hg] at he
  have hevent : ∀ᶠ z in 𝓝 (0 : Source 1), G z i = z 0 ^ a := by
    exact Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) he)
  let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  have hF : AnalyticAt ℂ F 0 :=
    hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _)
  have hsource : ∀ᶠ z in 𝓝 (0 : ℂ),
      curveParameterEquiv.symm z ∈ S ∧ F z i = z ^ a := by
    have ht := curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at ht
    exact ht.eventually (inter_mem hS hevent)
  obtain ⟨R, hR, hb⟩ := Metric.eventually_nhds_iff.mp
    (hF.eventually_analyticAt.and hsource)
  refine ⟨e, G, hG, hG0, hg, R, hR, ?_, ?_, ?_⟩
  · intro z hz
    exact (hb hz).1
  · intro z hz w hw hzw
    apply curveParameterEquiv.symm.injective
    exact hGi (hb hz).2.1 (hb hw).2.1 hzw
  · intro z hz
    exact (hb hz).2.2

/-- The circle in the fixed cylinder, obtained from the actual normalized
analytic representative and the coordinate complementary to `i`. -/
def curvePowerCylinderCircle (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) :
    Circle → Circle × ℂ := fun u => (u ^ a, F ((r : ℂ) * u) i.rev)

/-- Reinsert the fixed modulus of the projected coordinate. -/
def curvePowerCylinderReconstruction (i : Fin 2) (a : ℕ) (r : ℝ) :
    Circle × ℂ → Source 2 := fun p j =>
      if j = i then (r : ℂ) ^ a * (p.1 : ℂ) else p.2

theorem curvePowerCylinderCircle_projection
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) :
    Prod.fst ∘ curvePowerCylinderCircle F i a r = fun u => u ^ a := rfl

/-- Reconstruction in the fixed cylinder is exactly the original curve
on the parameter circle. -/
theorem curvePowerCylinderCircle_reconstruction
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) (u : Circle) :
    curvePowerCylinderReconstruction i a r (curvePowerCylinderCircle F i a r u) =
      F ((r : ℂ) * u) := by
  have hmem : (r : ℂ) * (u : ℂ) ∈ ball 0 R := by
    simpa [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrR
  ext j
  by_cases hji : j = i
  · subst j
    change (if i = i then (r : ℂ) ^ a * (u : ℂ) ^ a else _) = _
    rw [if_pos rfl, ← mul_pow, hp _ hmem]
  · have hj : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
    change (if j = i then _ else F ((r : ℂ) * u) i.rev) = _
    rw [if_neg hji, hj]

/-- The circle in the cylinder is a closed embedding because the analytic
representative is injective. -/
theorem curvePowerCylinderCircle_isClosedEmbedding
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hc : ContinuousOn F (ball 0 R)) (hi : InjOn F (ball 0 R))
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    Topology.IsClosedEmbedding (curvePowerCylinderCircle F i a r) := by
  have hmem (u : Circle) : (r : ℂ) * (u : ℂ) ∈ ball 0 R := by
    simpa [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrR
  have hcont : Continuous (fun u : Circle => F ((r : ℂ) * u)) :=
    hc.comp_continuous (by fun_prop) hmem
  apply (show Continuous (curvePowerCylinderCircle F i a r) from
    (continuous_pow a).prodMk (continuous_apply i.rev |>.comp hcont)).isClosedEmbedding
  intro u v huv
  apply Circle.ext
  apply mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
  apply hi (hmem u) (hmem v)
  simpa only [curvePowerCylinderCircle_reconstruction hr hrR hp] using
    congrArg (curvePowerCylinderReconstruction i a r) huv

/-- The actual cylinder circle has an `a`-sheeted covering projection. -/
theorem curvePowerCylinderCircle_covering
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a) (r : ℝ) :
    IsCoveringMap (Prod.fst ∘ curvePowerCylinderCircle F i a r) ∧
      ∀ v : Circle,
        Nat.card {u : Circle // (curvePowerCylinderCircle F i a r u).1 = v} = a :=
  ⟨circle_pow_isCoveringMap ha, circle_pow_fiber_card ha⟩

/-- The cylinder circle is smooth because its second component is the
restriction of an analytic representative. -/
theorem curvePowerCylinderCircle_contMDiff
    {F : ℂ → Source 2} (i : Fin 2) (a : ℕ) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hF : AnalyticOnNhd ℂ F (ball 0 R)) :
    ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (curvePowerCylinderCircle F i a r) := by
  have hparameter : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun u : Circle => (r : ℂ) * (u : ℂ)) :=
    (contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_coe_sphere
  have hsecond : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun u : Circle => F ((r : ℂ) * u) i.rev) := by
    intro u
    have hmem : (r : ℂ) * (u : ℂ) ∈ ball 0 R := by
      simpa [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrR
    have hscalar : AnalyticAt ℂ (fun z => F z i.rev) ((r : ℂ) * u) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i.rev).analyticAt _).comp
        (hF _ hmem)
    exact hscalar.restrictScalars.contDiffAt.contMDiffAt.comp u hparameter.contMDiffAt
  exact (contMDiff_pow a).prodMk hsecond

set_option backward.isDefEq.respectTransparency false in
/-- The ambient complex-valued angular power has injective differential
on the circle whenever its exponent is positive. -/
theorem circle_pow_coe_mfderiv_injective {a : ℕ} (ha : 0 < a) (u : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      (fun v : Circle => (v : ℂ) ^ a) u) := by
  let p : ℂ → ℂ := fun z => z ^ a
  have hd := (hasDerivAt_pow a (u : ℂ)).hasFDerivAt.restrictScalars ℝ
  have hi : Function.Injective (fderiv ℝ p (u : ℂ)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * ((a : ℂ) * (u : ℂ) ^ (a - 1)) =
      y * ((a : ℂ) * (u : ℂ) ^ (a - 1)) at hxy
    exact mul_right_cancel₀ (mul_ne_zero
      (show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne') (pow_ne_zero _ u.coe_ne_zero)) hxy
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v : Circle => (v : ℂ)) :=
    contMDiff_coe_sphere
  change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
    (p ∘ (fun v : Circle => (v : ℂ))) u)
  rw [mfderiv_comp u hd.differentiableAt.mdifferentiableAt
    (hcoe.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact hi.comp (injective_mvfderiv_subtypeVal_sphere u)

/-- The covering coordinate forces the cylinder circle to be immersed. -/
theorem curvePowerCylinderCircle_mfderiv_injective
    {F : ℂ → Source 2} (i : Fin 2) {a : ℕ} (ha : 0 < a) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hF : AnalyticOnNhd ℂ F (ball 0 R)) (u : Circle) :
    Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ))
      (curvePowerCylinderCircle F i a r) u) := by
  have hc := curvePowerCylinderCircle_contMDiff i a hr hrR hF
  have hp : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℂ => (p.1 : ℂ)) := contMDiff_coe_sphere.comp contMDiff_fst
  have hchain := mfderiv_comp u (hp.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  intro v w hvw
  apply circle_pow_coe_mfderiv_injective ha u
  change mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      ((fun p : Circle × ℂ => (p.1 : ℂ)) ∘ curvePowerCylinderCircle F i a r) u v =
    mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      ((fun p : Circle × ℂ => (p.1 : ℂ)) ∘ curvePowerCylinderCircle F i a r) u w
  rw [hchain]
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg _ hvw

/-- The circles in the cylinder are smooth embeddings, not merely
topological parametrizations of their images. -/
theorem curvePowerCylinderCircle_isSmoothEmbedding
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) (hi : InjOn F (ball 0 R))
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    Manifold.IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (curvePowerCylinderCircle F i a r) := by
  exact (curvePowerCylinderCircle_contMDiff i a hr hrR hF).isSmoothEmbedding_of_injective_mfderiv
    (by simp) (curvePowerCylinderCircle_mfderiv_injective i ha hr hrR hF)
    (curvePowerCylinderCircle_isClosedEmbedding hr hrR hF.continuousOn hi hp).isEmbedding

/-- A given injective branch germ with a component of order `a` determines
embedded circles in a fixed-radius cylinder, with exactly `a` sheets over
the angular coordinate. The reconstruction is the given germ after an
invertible analytic change of its source parameter. -/
theorem PointedMapGerm.exists_embedded_power_cylinder_circles
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
        AnalyticOnNhd ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
        (∀ z ∈ ball 0 R, F z i = z ^ a) ∧
        ∀ r : ℝ, 0 < r → r < R →
          Manifold.IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
            (curvePowerCylinderCircle F i a r) ∧
          Topology.IsClosedEmbedding (curvePowerCylinderCircle F i a r) ∧
          (∀ u, curvePowerCylinderReconstruction i a r (curvePowerCylinderCircle F i a r u) =
            F ((r : ℂ) * u)) ∧
          IsCoveringMap (Prod.fst ∘ curvePowerCylinderCircle F i a r) ∧
          ∀ v : Circle,
            Nat.card {u : Circle // (curvePowerCylinderCircle F i a r u).1 = v} = a := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, hF, hinj, hp⟩ :=
    β.exists_injective_power_representative hi i ha ho
  refine ⟨e, G, hG, hG0, hg, R, hR, hF, hinj, hp, ?_⟩
  intro r hr hrR
  exact ⟨curvePowerCylinderCircle_isSmoothEmbedding ha hr hrR hF hinj hp,
    curvePowerCylinderCircle_isClosedEmbedding hr hrR hF.continuousOn hinj hp,
    curvePowerCylinderCircle_reconstruction hr hrR hp,
    curvePowerCylinderCircle_covering _ i ha r⟩

/-- The multiplicity of the irreducible image equation is attained by one
of the two existing coordinate projections. -/
theorem PointedMapGerm.exists_component_order_of_irreducible_equation
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (f : Germ 2) (hf : Irreducible f) (hzero : β.pullbackRingHom f = 0)
    (a : ℕ) (ha : f ∈ Germ.maximalIdeal 2 ^ a)
    (ha' : f ∉ Germ.maximalIdeal 2 ^ (a + 1)) :
    ∃ i : Fin 2, Germ.vanishingOrder (β.1.component i) = a := by
  have hm := β.min_component_orders_eq_equation_order_of_injective_curve hi f hf hzero a ha ha'
  rcases le_total (Germ.vanishingOrder (β.1.component 0))
    (Germ.vanishingOrder (β.1.component 1)) with h | h
  · exact ⟨0, (min_eq_left h).symm.trans hm⟩
  · exact ⟨1, (min_eq_right h).symm.trans hm⟩

/-- The assembled singular-section data supplies an injective branch and
a coordinate of its exact multiplicity, bounded by the resolution weight.
Thus it satisfies the inputs of `exists_embedded_power_cylinder_circles`. -/
theorem SingularSectionPointData.exists_branch_component_order
    {H : Source 2 → Source 3} {x : Source 2} {m : ℕ}
    (h : SingularSectionPointData H x m) :
    ∃ (β : PointedMapGerm 1 2) (a : ℕ) (i : Fin 2),
      2 ≤ a ∧ a ≤ m ∧ β.HasInjectiveRepresentative ∧
      RingHom.ker β.pullbackRingHom = Ideal.span {localSectionEquation H x} ∧
      Germ.vanishingOrder (β.1.component i) = a := by
  obtain ⟨_, _, _, β, a, _, hirr, ha, ha', ha2, ham, _, _, hi, hker, _⟩ := h
  have hz : β.pullbackRingHom (localSectionEquation H x) = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (mem_singleton _)
  obtain ⟨i, ho⟩ := β.exists_component_order_of_irreducible_equation hi
    (localSectionEquation H x) hirr hz a ha ha'
  exact ⟨β, a, i, ha2, ham, hi, hker, ho⟩

/-- Every singular section in the analytic assembly determines an embedded
circle with a covering projection of degree its actual multiplicity `a ≤ m`.
Its analytic parametrization has exactly the assembled local equation as
pullback kernel. -/
theorem SingularSectionPointData.exists_embedded_power_cylinder_circle
    {H : Source 2 → Source 3} {x : Source 2} {m : ℕ}
    (h : SingularSectionPointData H x m) :
    ∃ (β : PointedMapGerm 1 2) (a : ℕ) (i : Fin 2)
      (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0) (r : ℝ),
      2 ≤ a ∧ a ≤ m ∧ 0 < r ∧
      RingHom.ker β.pullbackRingHom = Ideal.span {localSectionEquation H x} ∧
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
      (∀ u : Circle, AnalyticAt ℂ F ((r : ℂ) * u)) ∧
      Manifold.IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
        (curvePowerCylinderCircle F i a r) ∧
      Topology.IsClosedEmbedding (curvePowerCylinderCircle F i a r) ∧
      (∀ u, curvePowerCylinderReconstruction i a r (curvePowerCylinderCircle F i a r u) =
        F ((r : ℂ) * u)) ∧
      IsCoveringMap (Prod.fst ∘ curvePowerCylinderCircle F i a r) ∧
      ∀ v : Circle,
        Nat.card {u : Circle // (curvePowerCylinderCircle F i a r u).1 = v} = a := by
  obtain ⟨β, a, i, ha2, ham, hi, hker, ho⟩ := h.exists_branch_component_order
  have ha : 0 < a := lt_of_lt_of_le (by decide : 0 < 2) ha2
  obtain ⟨e, G, hG, hG0, hg, R, hR, hF, _, _, hcircles⟩ :=
    β.exists_embedded_power_cylinder_circles hi i ha ho
  refine ⟨β, a, i, e, G, hG, hG0, R / 2, ha2, ham, by positivity, hker, hg, ?_,
    hcircles (R / 2) (by positivity) (by linarith)⟩
  intro u
  apply hF
  simpa [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using
    (show R / 2 < R by linarith)

end OnLeConjecture.Analytic
