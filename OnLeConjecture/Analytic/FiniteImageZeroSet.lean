/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteFiberConfinement
public import OnLeConjecture.Analytic.PrincipalImageEquation
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proper representatives and closed analytic images

Compact confinement of the zero fibre supplies open source and target
neighborhoods on which a finite analytic map is proper. For a locally
injective representative this is a closed embedding. In dimension two into
three the image lies in the zero set of its irreducible germ equation.
Equality with that whole zero set is proved in `FinitePrincipalImage`.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

/-- Remove the image of a compact annulus to obtain a proper restriction
between open neighborhoods. The source neighborhood can be prescribed in
advance inside the compact set. -/
theorem exists_proper_restriction_of_compact_unique_fibre
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] [FirstCountableTopology Y]
    (F : X → Y) {K W : Set X} {V₀ : Set Y} {x₀ : X} {y₀ : Y}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hW : IsOpen W) (hxW : x₀ ∈ W) (hWK : W ⊆ interior K)
    (hV₀ : IsOpen V₀) (hyV₀ : y₀ ∈ V₀) (hzero : F x₀ = y₀)
    (hunique : ∀ x ∈ K, F x = y₀ → x = x₀) :
    ∃ (U : Set X) (V : Set Y) (hUV : MapsTo F U V),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      IsOpen V ∧ y₀ ∈ V ∧ V ⊆ V₀ ∧
      (∀ x ∈ K, F x ∈ V → x ∈ U) ∧
      IsProperMap (hUV.restrict F U V) := by
  let bad : Set X := K ∩ Wᶜ
  have hbad : IsCompact bad := hK.inter_right hW.isClosed_compl
  have hbadImage : IsCompact (F '' bad) :=
    hbad.image_of_continuousOn (hF.mono inter_subset_left)
  have hyBad : y₀ ∉ F '' bad := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (hunique x hx.1 heq ▸ hxW)
  let V := V₀ ∩ (F '' bad)ᶜ
  have hV : IsOpen V := hV₀.inter hbadImage.isClosed.isOpen_compl
  have hyV : y₀ ∈ V := ⟨hyV₀, hyBad⟩
  have hconfine : ∀ x ∈ K, F x ∈ V → x ∈ W := by
    intro x hx hxV
    by_contra hxW
    exact hxV.2 ⟨x, ⟨hx, hxW⟩, rfl⟩
  let U := interior K ∩ F ⁻¹' V
  have hU : IsOpen U :=
    (hF.mono interior_subset).isOpen_inter_preimage isOpen_interior hV
  have hUK : U ⊆ K := fun _ hx => interior_subset hx.1
  have hUV : MapsTo F U V := fun _ hx => hx.2
  refine ⟨U, V, hUV, hU, ⟨hWK hxW, by simpa only [Set.mem_preimage, hzero] using hyV⟩,
    (fun x hx => hconfine x (hUK hx) hx.2), hV, hyV,
    inter_subset_left, ?_, ?_⟩
  · intro x hx hxV
    exact ⟨hWK (hconfine x hx hxV), hxV⟩
  · rw [isProperMap_iff_isCompact_preimage]
    refine ⟨(continuousOn_iff_continuous_domRestrict.mp (hF.mono hUK)).subtype_mk _, ?_⟩
    intro C hC
    have hCval : IsCompact (Subtype.val '' C : Set Y) :=
      hC.image continuous_subtype_val
    have hpre : IsCompact (K ∩ F ⁻¹' (Subtype.val '' C)) :=
      hK.of_isClosed_subset
        (hF.preimage_isClosed_of_isClosed hK.isClosed hCval.isClosed)
        inter_subset_left
    rw [Subtype.isCompact_iff]
    convert hpre using 1
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hUK z.property, ⟨hUV.restrict F U V z, hz, rfl⟩⟩
    · rintro ⟨hxK, y, hyC, hxy⟩
      have hxV : F x ∈ V := hxy ▸ y.property
      let z : U := ⟨x, hWK (hconfine x hxK hxV), hxV⟩
      refine ⟨z, ?_, rfl⟩
      have heq : hUV.restrict F U V z = y := Subtype.ext hxy.symm
      change hUV.restrict F U V z ∈ C
      rwa [heq]

namespace PointedMapGerm

/-- Every finite plane germ has proper analytic restrictions between open
neighborhoods, inside any prescribed source and target neighborhoods. -/
theorem exists_proper_representative_restriction_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hfinite : g.IsFiniteAtOrigin)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0)
    (T : Set (Source m)) (hT : T ∈ 𝓝 0) :
    ∃ (U : Set (Source 2)) (V : Set (Source m)) (hUV : MapsTo G U V),
      IsOpen U ∧ 0 ∈ U ∧ U ⊆ S ∧ AnalyticOnNhd ℂ G U ∧
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ T ∧ IsProperMap (hUV.restrict G U V) := by
  obtain ⟨r, hr, hanalytic, hisolated⟩ :=
    g.exists_closedBall_isolated_zero_of_isFiniteAtOrigin hfinite G hG hG0 hg
  obtain ⟨W, hWS, hWopen, hW0⟩ := _root_.mem_nhds_iff.mp
    (inter_mem hS (ball_mem_nhds (0 : Source 2) hr))
  obtain ⟨V₀, hV₀T, hV₀open, hV₀0⟩ := _root_.mem_nhds_iff.mp hT
  have hWK : W ⊆ interior (closedBall (0 : Source 2) r) := by
    intro x hx
    exact ball_subset_interior_closedBall ((hWS hx).2)
  obtain ⟨U, V, hUV, hUopen, hU0, hUW, hVopen, hV0, hVV₀, _, hproper⟩ :=
    exists_proper_restriction_of_compact_unique_fibre G
      (isCompact_closedBall (0 : Source 2) r) hanalytic.continuousOn
      hWopen hW0 hWK hV₀open hV₀0 hG0 hisolated
  exact ⟨U, V, hUV, hUopen, hU0, fun x hx => (hWS (hUW hx)).1,
    hanalytic.mono (fun x hx => interior_subset (hWK (hUW hx))),
    hVopen, hV0, hVV₀.trans hV₀T, hproper⟩

/-- An injective finite plane representative restricts to a closed embedding
between open neighborhoods, inside any prescribed neighborhoods on which
it is injective. -/
theorem exists_closed_embedding_representative_restriction_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hfinite : g.IsFiniteAtOrigin)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S)
    (T : Set (Source m)) (hT : T ∈ 𝓝 0) :
    ∃ (U : Set (Source 2)) (V : Set (Source m)) (hUV : MapsTo G U V),
      IsOpen U ∧ 0 ∈ U ∧ U ⊆ S ∧ AnalyticOnNhd ℂ G U ∧
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ T ∧
      IsProperMap (hUV.restrict G U V) ∧
      Topology.IsClosedEmbedding (hUV.restrict G U V) := by
  obtain ⟨U, V, hUV, hU, hU0, hUS, hGU, hV, hV0, hVT, hp⟩ :=
    g.exists_proper_representative_restriction_of_finite hfinite G hG hG0 hg S hS T hT
  refine ⟨U, V, hUV, hU, hU0, hUS, hGU, hV, hV0, hVT, hp, ?_⟩
  rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
  refine ⟨hp.continuous, ?_, hp.isClosedMap⟩
  intro x y hxy
  apply Subtype.ext
  exact hinj (hUS x.property) (hUS y.property) (congrArg Subtype.val hxy)

/-- A locally injective plane germ in three-space has an irreducible equation
and representatives on open neighborhoods such that the map is proper and
a closed embedding into the target neighborhood, with its image contained
in that equation's zero set. The asserted ideal equality concerns all germs
of equations, and does not assert equality of representative sets. -/
theorem exists_closed_embedding_into_irreducible_zero_set
    (g : PointedMapGerm 2 3) (hinj : g.HasInjectiveRepresentative) :
    ∃ (f : Germ 3) (F : Source 3 → ℂ) (hF : AnalyticAt ℂ F 0),
      f = Germ.ofFunction F hF ∧ Irreducible f ∧ F 0 = 0 ∧
      RingHom.ker g.pullbackRingHom = Ideal.span {f} ∧
      ∃ (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
        g = ofFunction G hG hG0 ∧
        ∃ (U : Set (Source 2)) (V : Set (Source 3)) (hUV : MapsTo G U V),
          IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ G U ∧
          IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ F V ∧
          (∀ x ∈ U, F (G x) = 0) ∧
          IsProperMap (hUV.restrict G U V) ∧
          Topology.IsClosedEmbedding (hUV.restrict G U V) := by
  have hfinite := g.injective_isFiniteAtOrigin_two hinj
  obtain ⟨f, hf, hfm, hker⟩ := g.exists_irreducible_generator_of_finite hfinite
  obtain ⟨F, hF, hfF⟩ := Germ.exists_analyticRepresentative_allOrders f
  have hF0 : F 0 = 0 := by
    rw [hfF, Germ.mem_maximalIdeal_iff, Germ.valueRingHom_ofFunction] at hfm
    exact hfm
  obtain ⟨G, hG, hG0, hg, S, hS, hGS⟩ := hinj
  have hvanish : g.pullbackRingHom (Germ.ofFunction F hF) = 0 := by
    rw [← hfF]
    exact (show f ∈ RingHom.ker g.pullbackRingHom from
      hker ▸ Ideal.subset_span (Set.mem_singleton f))
  have hvanishevent : ∀ᶠ x in 𝓝 (0 : Source 2), F (G x) = 0 := by
    rw [hg] at hvanish
    exact Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 2 => q.1) hvanish)
  obtain ⟨U, V, hUV, hU, hU0, hUS, hGU, hV, hV0, hVT, hp, hemb⟩ :=
    g.exists_closed_embedding_representative_restriction_of_finite hfinite G hG hG0 hg
      (S ∩ {x | F (G x) = 0}) (inter_mem hS hvanishevent)
      (hGS.mono inter_subset_left)
      {y | AnalyticAt ℂ F y} hF.eventually_analyticAt
  exact ⟨f, F, hF, hfF, hf, hF0, hker, G, hG, hG0, hg,
    U, V, hUV, hU, hU0, hGU, hV, hV0, fun y hy => hVT hy,
    fun x hx => (hUS hx).2, hp, hemb⟩

end PointedMapGerm

end OnLeConjecture.Analytic
