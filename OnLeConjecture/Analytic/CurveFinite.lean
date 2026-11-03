/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveImage

/-!
# Finiteness of nonconstant analytic curve maps

A prepared equation for the parameter, followed by Weierstrass division,
expresses every source germ as a finite sum of parameter powers with
coefficients pulled back from the target. These powers generate the source
ring as a module over the image ring.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open LocalComplexGeometry ClassicalComplexWPT LocalComplexGeometry.WPTBridge

/-- A prepared parameter equation gives a fixed finite family of powers
that expresses every source germ with coefficients in the image ring. -/
theorem exists_curve_image_decomposition
    {m d : ℕ} (G : Source 1 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hd : 0 < d) (a : Fin d → Source m → ℂ)
    (ha : ∀ k, AnalyticAt ℂ (a k) 0) (ha0 : ∀ k, a k 0 = 0)
    (hprepared : ∀ᶠ x in 𝓝 0, preparedValue a (G x) (x 0) = 0)
    (f : Germ 1) :
    ∃ c : Fin d → (PointedMapGerm.ofFunction G hG hG0).ImageRing,
      f = ∑ k : Fin d, (c k : Germ 1) * Germ.coordinate 0 ^ (k : ℕ) := by
  obtain ⟨F, hF, rfl⟩ := Germ.exists_ofFunction f
  let H : ComplexEuclidean (m + 1) → ℂ := fun z => F (curveGraphSourceCLM m z)
  have hH : AnalyticAt ℂ H 0 := by
    apply hF.comp_of_eq ((curveGraphSourceCLM m).analyticAt 0)
    exact map_zero _
  let h := HolomorphicGerm.ofFunction H hH
  let q := preparedGermDivisionRemainder a ha ha0 h
  let B : Fin d → Source m → ℂ := HolomorphicGerm.coefficientRepresentatives q
  have hB (k : Fin d) : AnalyticAt ℂ (B k) 0 :=
    HolomorphicGerm.analyticAt_coefficientRepresentatives q k
  have hrepresentative : HolomorphicGerm.representative h =ᶠ[𝓝 0] H :=
    Filter.Germ.coe_eq.mp (HolomorphicGerm.coe_representative h)
  have hdivision : ∀ᶠ z in 𝓝 (0 : Source m), ∀ w : ℂ,
      preparedValue a z w = 0 → H (appendLastCLE m (z, w)) =
        ∑ k : Fin d, B k z * w ^ (k : ℕ) := by
    have hdv := eventually_representative_eq_remainder_on_preparedRoots hd a ha ha0 h
    have hrep := eventually_on_all_prepared_roots hd a ha ha0 hrepresentative
    filter_upwards [hdv, hrep] with z hzdiv hzrep
    intro w hw
    rw [← hzrep w hw, hzdiv w hw]
    rfl
  have hGt : Tendsto G (𝓝 0) (𝓝 (0 : Source m)) := by
    simpa only [hG0] using hG.continuousAt.tendsto
  have hsum : F =ᶠ[𝓝 0] fun x => ∑ k : Fin d, B k (G x) * (x 0) ^ (k : ℕ) := by
    filter_upwards [hGt.eventually hdivision, hprepared] with x hx hp
    have h := hx (x 0) hp
    have hvec : (fun _ : Fin 1 => x 0) = x := by
      ext j
      exact congrArg x (Subsingleton.elim _ _)
    simpa only [H, curveGraphSourceCLM_appendLastCLE, hvec] using h
  let g := PointedMapGerm.ofFunction G hG hG0
  let c : Fin d → g.ImageRing := fun k =>
    g.pullbackToImageRing (Germ.ofFunction (B k) (hB k))
  refine ⟨c, ?_⟩
  apply Subtype.ext
  calc
    ((Germ.ofFunction F hF : Germ 1) : FunctionGerm 1) =
        ((fun x => ∑ k : Fin d, B k (G x) * (x 0) ^ (k : ℕ)) : FunctionGerm 1) :=
      Filter.Germ.coe_eq.mpr hsum
    _ = ∑ k : Fin d, ((fun x => B k (G x) * (x 0) ^ (k : ℕ)) : FunctionGerm 1) := by
      rw [show (fun x => ∑ k : Fin d, B k (G x) * (x 0) ^ (k : ℕ)) =
          ∑ k : Fin d, (fun x => B k (G x) * (x 0) ^ (k : ℕ)) by
        funext x
        simp only [Finset.sum_apply]]
      exact Germ.coe_sum (𝓝 (0 : Source 1)) ℂ
        (fun k => fun x => B k (G x) * (x 0) ^ (k : ℕ)) Finset.univ
    _ = ∑ k : Fin d, (((c k : Germ 1) * Germ.coordinate 0 ^ (k : ℕ) : Germ 1) :
        FunctionGerm 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rfl
    _ = ((∑ k : Fin d, (c k : Germ 1) * Germ.coordinate 0 ^ (k : ℕ) : Germ 1) :
        FunctionGerm 1) :=
      (map_sum (analyticGermSubring 1).subtype
        (fun k : Fin d => (c k : Germ 1) * Germ.coordinate 0 ^ (k : ℕ)) Finset.univ).symm

namespace PointedMapGerm

/-- A locally injective curve cannot have every component equal to the zero germ. -/
theorem exists_nonzero_coordinate_pullback_of_injective_curve {m : ℕ}
    (g : PointedMapGerm 1 m) (hi : g.HasInjectiveRepresentative) :
    ∃ i, g.pullbackRingHom (Germ.coordinate i) ≠ 0 := by
  obtain ⟨G, hG, hG0, rfl, S, hS, hGin⟩ := hi
  by_contra h
  push Not at h
  have hz (i : Fin m) : ∀ᶠ x in 𝓝 (0 : Source 1), G x i = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) (h i))
  have hzero : ∀ᶠ x in 𝓝 (0 : Source 1), x = 0 := by
    filter_upwards [Filter.eventually_all.mpr hz, hS] with x hx hxS
    apply hGin hxS (mem_of_mem_nhds hS)
    rw [hG0]
    exact funext hx
  apply Germ.coordinate_ne_zero (0 : Fin 1)
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hzero] with x hx
  rw [hx]
  rfl

/-- Every nonconstant analytic map from a smooth curve is finite over its image ring. -/
theorem isFiniteAtOrigin_of_nonconstant_curve {m : ℕ} (g : PointedMapGerm 1 m)
    (hn : ∃ i, g.pullbackRingHom (Germ.coordinate i) ≠ 0) : g.IsFiniteAtOrigin := by
  obtain ⟨G, hG, hG0, rfl⟩ := g.exists_ofFunction
  obtain ⟨i, hi⟩ := hn
  obtain ⟨d, hd, a, ha, ha0, hprepared⟩ :=
    exists_curve_parameter_prepared_equation G hG hG0 i hi
  let g := PointedMapGerm.ofFunction G hG hG0
  let v : Fin d → Germ 1 := fun k => Germ.coordinate 0 ^ (k : ℕ)
  have hspan : Submodule.span g.ImageRing (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro f hf
    obtain ⟨c, hc⟩ := exists_curve_image_decomposition G hG hG0 hd a ha ha0 hprepared f
    rw [hc]
    apply Submodule.sum_mem
    intro k hk
    have hv : v k ∈ Submodule.span g.ImageRing (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self k)
    have hs := Submodule.smul_mem (Submodule.span g.ImageRing (Set.range v)) (c k) hv
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubring] at hs
    exact hs
  refine ⟨?_⟩
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range v)

/-- A locally injective curve is finite over its image ring. -/
theorem isFiniteAtOrigin_of_injective_curve {m : ℕ} (g : PointedMapGerm 1 m)
    (hi : g.HasInjectiveRepresentative) : g.IsFiniteAtOrigin :=
  g.isFiniteAtOrigin_of_nonconstant_curve
    (g.exists_nonzero_coordinate_pullback_of_injective_curve hi)

end PointedMapGerm
end OnLeConjecture.Analytic
