/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionFloerReduction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The exterior of an assembled nearby section

The source domain is the literal source norm ball cut by the first coordinate
of the assembled map. The two remaining target coordinates define an injective
map of that level. Outside its enumerated critical points the differential on
the source-level tangent has complex rank one. Analyticity on a closed source
ball is retained by choosing the nearby level at a smaller radius.

No identification with the preimage of a target ball, boundary-compatible
cobordism, or genus computation is asserted.
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace ResolutionSectionAssembly

/-- The two target coordinates on a section of the assembled map. -/
def sectionMap (A : ResolutionSectionAssembly g hd hi) : Source 2 → Source 2 :=
  fun x => hyperplaneTail 2 (A.H x)

theorem sectionMap_analyticAt (A : ResolutionSectionAssembly g hd hi)
    {x : Source 2} (hx : AnalyticAt ℂ A.H x) : AnalyticAt ℂ A.sectionMap x :=
  ((hyperplaneTail 2).analyticAt _).comp hx

theorem sectionMap_fderiv (A : ResolutionSectionAssembly g hd hi)
    {x : Source 2} (hx : DifferentiableAt ℂ A.H x) :
    fderiv ℂ A.sectionMap x = (hyperplaneTail 2).comp (fderiv ℂ A.H x) :=
  ((hyperplaneTail 2).hasFDerivAt.comp x hx.hasFDerivAt).fderiv

/-- Keeping the first target coordinate fixed recovers the original map exactly. -/
theorem sectionMap_reconstruction (A : ResolutionSectionAssembly g hd hi)
    {x : Source 2} {s : ℂ} (hx : A.H x 0 = s) :
    Fin.cons s (A.sectionMap x) = A.H x := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact hx.symm
  · rfl

/-- Analyticity of the chosen representative is retained at a smaller source
radius, together with a genuine nearby level from the assembly. -/
theorem exists_analytic_level (A : ResolutionSectionAssembly g hd hi) :
    ∃ L : ResolutionSectionLevel A,
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius) := by
  obtain ⟨R, hR, hanalytic⟩ := Metric.mem_nhds_iff.mp A.H_analytic.eventually_analyticAt
  let r : ℝ := min A.radius (R / 2)
  have hr : 0 < r := lt_min A.radius_pos (half_pos hR)
  obtain ⟨L, hL⟩ := A.exists_level_at_radius r hr (min_le_left _ _)
  refine ⟨L, ?_⟩
  intro x hx
  apply hanalytic
  rw [mem_ball, dist_zero_right]
  have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right, hL] using hx
  exact hn.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hR))

end ResolutionSectionAssembly

namespace ResolutionSectionLevel

variable {A : ResolutionSectionAssembly g hd hi} (L : ResolutionSectionLevel A)

/-- The compact-domain level already used in the assembly's closed embedding. -/
def sourceLevel : Set (Source 2) :=
  closedBall (0 : Source 2) L.radius ∩ (fun x => A.H x 0) ⁻¹' {L.parameter}

/-- The interior of the source norm ball on the same exact level. -/
def sourceInterior : Set (Source 2) :=
  ball (0 : Source 2) L.radius ∩ (fun x => A.H x 0) ⁻¹' {L.parameter}

/-- The source-level tangent is the kernel of the first component's differential. -/
def sectionTangent (_L : ResolutionSectionLevel A) (x : Source 2) : Submodule ℂ (Source 2) :=
  LinearMap.ker (fderiv ℂ (fun y => A.H y 0) x).toLinearMap

/-- The actual differential of the two-coordinate map restricted to the level tangent. -/
def sectionTangentMap (x : Source 2) : L.sectionTangent x →ₗ[ℂ] Source 2 :=
  (fderiv ℂ A.sectionMap x).toLinearMap.comp (L.sectionTangent x).subtype

theorem sectionMap_injOn : InjOn A.sectionMap L.sourceLevel := by
  intro x hx y hy hxy
  have heq : (L.sourceLevel.domRestrict A.H) ⟨x, hx⟩ =
      (L.sourceLevel.domRestrict A.H) ⟨y, hy⟩ := by
    change A.H x = A.H y
    rw [← A.sectionMap_reconstruction hx.2, ← A.sectionMap_reconstruction hy.2, hxy]
  exact congrArg Subtype.val (L.closedEmbedding.injective heq)

/-- The source level is embedded in its literal two-coordinate target plane. -/
theorem sectionMap_closedEmbedding :
    Topology.IsClosedEmbedding (L.sourceLevel.domRestrict A.sectionMap) := by
  have hc : Continuous (fun y : Source 2 => (Fin.cons L.parameter y : Source 3)) := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact continuous_const
    · exact continuous_apply k
  have hleft : LeftInverse (hyperplaneTail 2)
      (fun y : Source 2 => (Fin.cons L.parameter y : Source 3)) :=
    fun _ => rfl
  have hemb : Topology.IsEmbedding (fun y : Source 2 => (Fin.cons L.parameter y : Source 3)) :=
    hleft.isEmbedding (hyperplaneTail 2).continuous hc
  apply Topology.IsClosedEmbedding.of_comp hemb
  have heq : (fun y : Source 2 => (Fin.cons L.parameter y : Source 3)) ∘
      L.sourceLevel.domRestrict A.sectionMap = L.sourceLevel.domRestrict A.H := by
    funext x
    exact A.sectionMap_reconstruction x.property.2
  rw [heq]
  exact L.closedEmbedding

/-- The section image equation keeps the source norm condition explicitly. -/
theorem mem_sectionMap_image_iff {y : Source 2} :
    y ∈ A.sectionMap '' L.sourceLevel ↔
      ∃ x ∈ closedBall (0 : Source 2) L.radius, A.H x = Fin.cons L.parameter y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, (A.sectionMap_reconstruction hx.2).symm⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · exact congrFun hxy 0
    · exact congrArg (hyperplaneTail 2) hxy

/-- The complete critical-point enumeration gives injectivity of the ambient
differential at every remaining interior level point. -/
theorem fderiv_injective_of_not_mem_points {x : Source 2}
    (hx : x ∈ L.sourceInterior) (hxZ : x ∉ L.points) :
    Injective (fderiv ℂ A.H x) := by
  by_contra hn
  exact hxZ ((L.points_iff x).mpr ⟨hx.1, hx.2, hn⟩)

theorem sectionTangent_finrank {x : Source 2} (hx : x ∈ L.sourceInterior) :
    Module.finrank ℂ (L.sectionTangent x) = 1 := by
  have hn := (L.regular x hx.1 hx.2).1
  have hn' : (fderiv ℂ (fun y => A.H y 0) x).toLinearMap ≠ 0 := by
    intro he
    apply hn
    exact ContinuousLinearMap.coe_injective he
  have h := (fderiv ℂ (fun y => A.H y 0) x).toLinearMap.finrank_range_add_finrank_ker
  rw [Module.Dual.range_eq_top_of_ne_zero hn', finrank_top, Module.finrank_self] at h
  have hdim : Module.finrank ℂ (Source 2) = 2 := by simp [Source]
  change Module.finrank ℂ (L.sectionTangent x) = 1
  change 1 + Module.finrank ℂ (L.sectionTangent x) = Module.finrank ℂ (Source 2) at h
  omega

/-- Dropping the fixed first target coordinate does not kill a nonzero
source-level tangent away from the enumerated critical points. -/
theorem sectionTangentMap_injective {x : Source 2}
    (hx : x ∈ L.sourceInterior) (hxZ : x ∉ L.points)
    (hA : AnalyticAt ℂ A.H x) : Injective (L.sectionTangentMap x) := by
  intro v w hvw
  apply Subtype.ext
  apply L.fderiv_injective_of_not_mem_points hx hxZ
  have hfirst : fderiv ℂ (fun y => A.H y 0) x =
      (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).comp (fderiv ℂ A.H x) :=
    by
      have hp : HasFDerivAt (fun z : Source 3 => z 0)
          (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)) (A.H x) :=
        hasFDerivAt_apply (0 : Fin 3) (A.H x)
      exact (hp.comp x hA.differentiableAt.hasFDerivAt).fderiv
  have hv : fderiv ℂ A.H x v 0 = 0 := by
    have hv := v.property
    change fderiv ℂ (fun y => A.H y 0) x v = 0 at hv
    simpa only [hfirst, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hv
  have hw : fderiv ℂ A.H x w 0 = 0 := by
    have hw := w.property
    change fderiv ℂ (fun y => A.H y 0) x w = 0 at hw
    simpa only [hfirst, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hw
  change fderiv ℂ A.sectionMap x v = fderiv ℂ A.sectionMap x w at hvw
  rw [A.sectionMap_fderiv hA.differentiableAt] at hvw
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact hv.trans hw.symm
  · exact congrFun hvw k

theorem sectionTangentMap_rank_one {x : Source 2}
    (hx : x ∈ L.sourceInterior) (hxZ : x ∉ L.points)
    (hA : AnalyticAt ℂ A.H x) :
    Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 :=
  (LinearMap.finrank_range_of_inj (L.sectionTangentMap_injective hx hxZ hA)).trans
    (L.sectionTangent_finrank hx)

/-- Every omitted neighborhood containing the complete critical set leaves
an injective rank-one tangent map on the exterior of the source level. -/
theorem exterior_tangent_properties
    (hA : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    {U : Set (Source 2)} (hU : (L.points : Set (Source 2)) ⊆ U)
    {x : Source 2} (hx : x ∈ L.sourceInterior \ U) :
    AnalyticAt ℂ A.sectionMap x ∧
      fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
      Injective (L.sectionTangentMap x) ∧
      Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 := by
  have hxa := hA x (ball_subset_closedBall hx.1.1)
  have hxZ : x ∉ L.points := fun h => hx.2 (hU h)
  exact ⟨A.sectionMap_analyticAt hxa, (L.regular x hx.1.1 hx.1.2).1,
    L.sectionTangentMap_injective hx.1 hxZ hxa,
    L.sectionTangentMap_rank_one hx.1 hxZ hxa⟩

/-- A smaller closed source cut lies inside the proven regularity domain,
including its source-sphere boundary. This is not a transversality assertion. -/
theorem exterior_closedCut_tangent_properties
    (hA : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    {r : ℝ} (hr : r < L.radius)
    {U : Set (Source 2)} (hU : (L.points : Set (Source 2)) ⊆ U)
    {x : Source 2} (hx : x ∈ closedBall (0 : Source 2) r)
    (hlevel : A.H x 0 = L.parameter) (hxU : x ∉ U) :
    AnalyticAt ℂ A.sectionMap x ∧
      fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
      Injective (L.sectionTangentMap x) ∧
      Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 :=
  L.exterior_tangent_properties hA hU
    ⟨⟨closedBall_subset_ball hr hx, hlevel⟩, hxU⟩

/-- The image of any part of the level is exactly the specified affine-plane
image, with the source-domain restriction still present. -/
theorem mem_sectionMap_image_subset_iff {S : Set (Source 2)}
    (hS : S ⊆ L.sourceLevel) {y : Source 2} :
    y ∈ A.sectionMap '' S ↔ ∃ x ∈ S, A.H x = Fin.cons L.parameter y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (A.sectionMap_reconstruction (hS hx).2).symm⟩
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, congrArg (hyperplaneTail 2) heq⟩

end ResolutionSectionLevel

namespace ResolutionSectionAssembly

/-- The analytic assembly constructs a nearby section with a closed embedded
two-coordinate image and a rank-one injective differential on its exterior.
The neighborhood removed from the source need only contain the explicitly
enumerated critical points. Analyticity is derived by shrinking the radius. -/
theorem exists_exterior_section_data (A : ResolutionSectionAssembly g hd hi) :
    ∃ L : ResolutionSectionLevel A,
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius) ∧
      InjOn A.sectionMap L.sourceLevel ∧
      Topology.IsClosedEmbedding (L.sourceLevel.domRestrict A.sectionMap) ∧
      (∀ y : Source 2, y ∈ A.sectionMap '' L.sourceLevel ↔
        ∃ x ∈ closedBall (0 : Source 2) L.radius, A.H x = Fin.cons L.parameter y) ∧
      ∀ U : Set (Source 2), (L.points : Set (Source 2)) ⊆ U →
        ∀ x ∈ L.sourceInterior \ U,
          AnalyticAt ℂ A.sectionMap x ∧
          fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
          Injective (L.sectionTangentMap x) ∧
          Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 := by
  obtain ⟨L, hL⟩ := A.exists_analytic_level
  exact ⟨L, hL, L.sectionMap_injOn, L.sectionMap_closedEmbedding,
    fun _ => L.mem_sectionMap_image_iff,
    fun _ hU _ hx => L.exterior_tangent_properties hL hU hx⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
