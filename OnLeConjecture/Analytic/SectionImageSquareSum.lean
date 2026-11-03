/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TargetLinearSpan
public import OnLeConjecture.Analytic.SectionImageRepresentative
public import OnLeConjecture.Analytic.RawWeakBlowupCompanionIntersection
public import OnLeConjecture.Analytic.RawWeakBlowupReducedMembers
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# The image section multiplicity is the original tree square sum

A reduced exact member is made the first coordinate by a target linear
change. The original weak-blowup tree is retained. A second companion is
chosen to attain the minimum order on every source branch normalization.
Its source intersection is the tree square sum, and the image intersection
then computes the exact order of the constructed reduced plane image.
-/

public noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

namespace RawProjectiveWeakBlowupTree

/-- The exact order of the image of a reduced exact member equals the
square sum on the original tree. No coordinate change of that tree is needed. -/
theorem exists_sectionImageFactorization_exact_squareSum
    {g : PointedMapGerm 2 3} (T : RawProjectiveWeakBlowupTree g.1.component)
    (hg : g.HasInjectiveRepresentative) (q₀ : Fin 3 → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsq : Squarefree (germLinearCombination g.1.component q₀)) :
    ∃ (f : PointedMapGerm 2 3) (D : SectionImageFactorization f),
      g.RightLeftEquivalent f ∧
      f.1.component 0 = germLinearCombination g.1.component q₀ ∧
      Submodule.span ℂ (Set.range f.1.component) =
        Submodule.span ℂ (Set.range g.1.component) ∧
      Squarefree D.imageEquation ∧
      D.imageEquation ∈ maximalIdeal 2 ^ (∑ p, (T.multiplicity p) ^ 2) ∧
      D.imageEquation ∉ maximalIdeal 2 ^ ((∑ p, (T.multiplicity p) ^ 2) + 1) := by
  classical
  have hqne : q₀ ≠ 0 := by
    intro hz
    apply hq₀ T.root
    rw [hz, map_zero]
    exact Ideal.zero_mem _
  obtain ⟨r₀, _, hfinite₀, _⟩ := T.exists_companion_intersection_eq_squareSum_mem_open
    q₀ hq₀ Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
  obtain ⟨f, hgf, hf₀, _, hspan⟩ :=
    exists_target_pair_with_span_eq g q₀ r₀ hqne hfinite₀
  have hfi := hgf.hasInjectiveRepresentative hg
  obtain ⟨D⟩ := f.exists_sectionImageFactorization hfi (hf₀ ▸ hsq)
  have hnonzero (i : D.branches) : ∃ j, (D.parametrization i).pullbackRingHom
      (g.1.component j) ≠ 0 := by
    have hi := g.comp_hasInjectiveRepresentative (D.parametrization i) hg
      (D.parametrizationInjective i)
    obtain ⟨j, hj⟩ := PointedMapGerm.exists_nonzero_coordinate_pullback_of_injective_curve
      (g.comp (D.parametrization i)) hi
    refine ⟨j, ?_⟩
    simpa only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      PointedMapGerm.pullback_coordinate] using hj
  obtain ⟨U, hU, hUdense, hUorder⟩ :=
    exists_open_dense_pullback_combinations_minimum_order g.1.component D.parametrization hnonzero
  obtain ⟨r, hr, hfinite, hinter⟩ := T.exists_companion_intersection_eq_squareSum_mem_open
    q₀ hq₀ U hU hUdense.nonempty
  have hmem : germLinearCombination g.1.component r ∈
      Submodule.span ℂ (Set.range f.1.component) := by
    rw [hspan]
    change (∑ j, r j • g.1.component j) ∈ _
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  obtain ⟨c, a, hdecomp⟩ :=
    exists_plane_linear_form_mod_first_component f _ hmem
  let q : Germ 2 := germLinearCombination (coordinate : Fin 2 → Germ 2) c
  let u := germLinearCombination g.1.component r
  let w := f.pullbackRingHom (hyperplaneExtension 2 q)
  have hdecomp' : u = w + a • f.1.component 0 := hdecomp
  have hsub : u - f.1.component 0 * constRingHom 2 a = w := by
    rw [hdecomp']
    change w + constRingHom 2 a * f.1.component 0 - f.1.component 0 * constRingHom 2 a = w
    ring
  have hideal : pairIdeal (f.1.component 0) w = pairIdeal (f.1.component 0) u := by
    rw [← hsub]
    exact pairIdeal_sub_mul_right _ _ _
  have hfiniteu : HasFiniteIntersection (f.1.component 0) u := by
    rwa [hf₀]
  have hfinitew := hfiniteu.of_pairIdeal_eq hideal.symm
  have hminimum (i : D.branches) :
      vanishingOrder ((D.parametrization i).pullbackRingHom w) =
        ⨅ j : Fin 3, vanishingOrder ((D.parametrization i).pullbackRingHom (f.1.component j)) := by
    have hpull : (D.parametrization i).pullbackRingHom u =
        (D.parametrization i).pullbackRingHom w := by
      rw [hdecomp', map_add, PointedMapGerm.pullback_complex_smul,
        D.section_zero i, smul_zero, add_zero]
    rw [← hpull, hUorder r hr i]
    exact (iInf_pullback_order_eq_of_span_eq (D.parametrization i)
      f.1.component g.1.component hspan).symm
  have hexact := D.imageEquation_exact_order_of_minimum hfi q hfinitew hminimum
  have hsum : intersectionMultiplicity (f.1.component 0) w hfinitew =
      ∑ p, (T.multiplicity p) ^ 2 := by
    rw [intersectionMultiplicity_eq_of_pairIdeal_eq hfinitew hfiniteu hideal]
    have h := hinter.trans (T.pointBasis_squareSum q₀ hq₀)
    simpa only [hf₀, u] using h
  rw [hsum] at hexact
  exact ⟨f, D, hgf, hf₀, hspan, D.imageEquation_squarefree hfi, hexact⟩

/-- Every constructed tree of an injective plane map has a reduced plane
section image whose multiplicity is its square sum. The equation describes
the entire nearby image on an injective analytic representative. -/
theorem exists_reduced_section_image_exact_squareSum
    {g : PointedMapGerm 2 3} (T : RawProjectiveWeakBlowupTree g.1.component)
    (hg : g.HasInjectiveRepresentative) :
    ∃ (q₀ : Fin 3 → ℂ) (f : PointedMapGerm 2 3)
      (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
      (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0) (r : ℝ),
      g.RightLeftEquivalent f ∧ f = PointedMapGerm.ofFunction G hG hG0 ∧
      f.1.component 0 = germLinearCombination g.1.component q₀ ∧
      Squarefree (ofFunction W hW) ∧
      ofFunction W hW ∈ maximalIdeal 2 ^ (∑ p, (T.multiplicity p) ^ 2) ∧
      ofFunction W hW ∉ maximalIdeal 2 ^ ((∑ p, (T.multiplicity p) ^ 2) + 1) ∧
      0 < r ∧ AnalyticOnNhd ℂ G (Metric.closedBall 0 r) ∧
      Set.InjOn G (Metric.closedBall 0 r) ∧
      ∀ᶠ y in 𝓝 (0 : Source 2),
        W y = 0 ↔ ∃ x ∈ Metric.closedBall (0 : Source 2) r,
          G x = hyperplaneInclusion 2 y := by
  obtain ⟨U, _, ⟨q₀, hqU⟩, _, hU⟩ :=
    T.exists_open_reduced_members Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
  have hq₀ := fun p => (hU q₀ hqU p).1
  have hsq : Squarefree (germLinearCombination g.1.component q₀) := by
    simpa only [T.generators_root] using (hU q₀ hqU T.root).2
  obtain ⟨f, D, hgf, hf₀, _, hWsq, hWm, hWnext⟩ :=
    T.exists_sectionImageFactorization_exact_squareSum hg q₀ hq₀ hsq
  have hfi := hgf.hasInjectiveRepresentative hg
  obtain ⟨G, hG, hG0, hfG, S, hS, hGin⟩ := hfi
  obtain ⟨W, hW, hWeq⟩ := exists_ofFunction D.imageEquation
  obtain ⟨r, hr, hrS, hGr, hcoverage⟩ :=
    D.exists_closedBall_section_image_eq_zero_set (hgf.hasInjectiveRepresentative hg)
      G hG hG0 hfG W hW hWeq S hS
  exact ⟨q₀, f, G, hG, hG0, W, hW, r, hgf, hfG, hf₀,
    hWeq ▸ hWsq, hWeq ▸ hWm, hWeq ▸ hWnext, hr, hGr, hGin.mono hrS, hcoverage⟩

end RawProjectiveWeakBlowupTree
end OnLeConjecture.Analytic
