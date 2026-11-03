/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupCodimension
public import OnLeConjecture.Analytic.NormalizationComparison
public import OnLeConjecture.Analytic.InjectiveIntersectionParametrization
public import OnLeConjecture.Analytic.MilnorBlowupRecurrence
public import OnLeConjecture.Analytic.GenericReducedPencil
public import OnLeConjecture.Analytic.RegularBlowupCharts
public import OnLeConjecture.Analytic.ProjectiveIrreducibleBlowupBranch

/-!
# The normalization quotient of an irreducible plane branch

Let `γ` be a locally injective nonconstant parametrization of the curve of
an irreducible plane equation `f`. The pullback `γ^* : ℂ{x, y} → ℂ{t}` has
kernel `(f)`, so its image is a subring of the discrete valuation ring
`ℂ{t}` isomorphic to `ℂ{x, y}/(f)`.

Two such parametrizations differ by a complex algebra automorphism of
`ℂ{t}` carrying one image onto the other. Hence the complex dimension of
`ℂ{t}/γ^* ℂ{x, y}` depends only on `f`.

Along a finite chain of coordinate changes and point blowups ending at a
smooth branch, this dimension is finite. At a blowup of a branch of
multiplicity `m`, it drops by `0 + 1 + ⋯ + (m - 1)`. The Milnor branch
quantity `μ + b - 1` drops by `m (m - 1)` at the same step. Consequently
twice the dimension equals `μ + b - 1 = μ` for every irreducible equation.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Module

namespace PointedMapGerm

/-- The complex subspace `γ^* ℂ{x, y}` of `ℂ{t}`. -/
noncomputable def pullbackImage (γ : PointedMapGerm 1 2) : Submodule ℂ (Germ 1) :=
  LinearMap.range γ.pullbackAlgHom.toLinearMap

/-- A locally injective nonconstant curve germ along which `f` vanishes. -/
def IsInjectiveParametrizationOf (γ : PointedMapGerm 1 2) (f : Germ 2) : Prop :=
  γ.HasInjectiveRepresentative ∧ γ.pullbackRingHom f = 0 ∧
    ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0

theorem ker_pullbackAlgHom_toLinearMap {f : Germ 2} (hf : Irreducible f) {γ : PointedMapGerm 1 2}
    (hγ : γ.IsInjectiveParametrizationOf f) :
    LinearMap.ker γ.pullbackAlgHom.toLinearMap = (Ideal.span {f}).restrictScalars ℂ := by
  ext g
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem,
    ← parametrization_kernel_eq_span_singleton f hf γ hγ.2.1 hγ.2.2, RingHom.mem_ker]
  rfl

/-- Two injective parametrizations of an irreducible equation have
linearly isomorphic normalization quotients. -/
theorem nonempty_quotient_pullbackImage_equiv {f : Germ 2} (hf : Irreducible f)
    {γ γ' : PointedMapGerm 1 2} (hγ : γ.IsInjectiveParametrizationOf f)
    (hγ' : γ'.IsInjectiveParametrizationOf f) :
    Nonempty ((Germ 1 ⧸ γ.pullbackImage) ≃ₗ[ℂ] (Germ 1 ⧸ γ'.pullbackImage)) := by
  have hker : RingHom.ker γ.pullbackRingHom = RingHom.ker γ'.pullbackRingHom := by
    rw [parametrization_kernel_eq_span_singleton f hf γ hγ.2.1 hγ.2.2,
      parametrization_kernel_eq_span_singleton f hf γ' hγ'.2.1 hγ'.2.2]
  obtain ⟨e, he⟩ := γ.exists_normalization_ringEquiv γ'
    (γ.isFiniteAtOrigin_of_injective_curve hγ.1) (γ'.isFiniteAtOrigin_of_injective_curve hγ'.1)
    (γ.isBirationalAtOrigin_of_injective_curve hγ.1)
    (γ'.isBirationalAtOrigin_of_injective_curve hγ'.1) hker
  let eA : Germ 1 ≃ₐ[ℂ] Germ 1 := AlgEquiv.ofRingEquiv (f := e) (fun c => by
    have h := he (constRingHom 2 c)
    rwa [γ.pullback_constRingHom, γ'.pullback_constRingHom] at h)
  have hcomp : eA.toLinearEquiv.toLinearMap ∘ₗ γ.pullbackAlgHom.toLinearMap =
      γ'.pullbackAlgHom.toLinearMap :=
    LinearMap.ext fun g => he g
  have hmap : γ.pullbackImage.map (eA.toLinearEquiv : Germ 1 →ₗ[ℂ] Germ 1) =
      γ'.pullbackImage := by
    rw [pullbackImage, pullbackImage, ← hcomp, LinearMap.range_comp]
  exact ⟨Submodule.Quotient.equiv _ _ eA.toLinearEquiv hmap⟩

end PointedMapGerm

namespace Germ

/-- A finite smooth blowup chain gives an injective parametrization whose
normalization quotient is finite dimensional of dimension half the Milnor
branch quantity. -/
theorem HasFiniteSmoothBlowupChain.exists_parametrization_two_mul_finrank {f : Germ 2}
    (hchain : HasFiniteSmoothBlowupChain f) (hirr : Irreducible f) :
    ∃ γ : PointedMapGerm 1 2, γ.IsInjectiveParametrizationOf f ∧
      FiniteDimensional ℂ (Germ 1 ⧸ γ.pullbackImage) ∧
      2 * finrank ℂ (Germ 1 ⧸ γ.pullbackImage) = milnorBranchDefect f := by
  induction hchain with
  | smooth f hf hn =>
    obtain ⟨e, he⟩ := exists_equiv_pullback_eq_coordinate f hf
      (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).1
    let γ := e.forward.comp (hyperplaneInclusionGerm 1)
    have hcurve : γ.pullbackRingHom f = 0 := by
      rw [PointedMapGerm.pullbackRingHom_comp]
      change hyperplaneRestriction 1 (e.pullbackAlgEquiv f) = 0
      rw [he, hyperplaneRestriction_coordinate_zero]
    have hnc : ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0 := by
      apply PointedMapGerm.exists_nonzero_coordinate_pullback_comp_equiv
      refine ⟨1, ?_⟩
      change hyperplaneRestriction 1 (coordinate (1 : Fin 2)) ≠ 0
      simpa only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
        hyperplaneRestriction_coordinate_succ] using coordinate_zero_ne_zero
    have hinj : γ.HasInjectiveRepresentative :=
      e.forward.comp_hasInjectiveRepresentative (hyperplaneInclusionGerm 1)
        e.forward_hasInjectiveRepresentative (hyperplaneInclusionGerm_hasInjectiveRepresentative 1)
    have htop : γ.pullbackImage = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨g, hg⟩ := hyperplaneRestriction_surjective 1 x
      obtain ⟨g', hg'⟩ := e.pullbackAlgEquiv.surjective g
      refine ⟨g', ?_⟩
      change γ.pullbackRingHom g' = x
      rw [PointedMapGerm.pullbackRingHom_comp]
      change hyperplaneRestriction 1 (e.pullbackAlgEquiv g') = x
      rw [hg', hg]
    have hsub : Subsingleton (Germ 1 ⧸ γ.pullbackImage) := by
      rw [htop]
      infer_instance
    refine ⟨γ, ⟨hinj, hcurve, hnc⟩, inferInstance, ?_⟩
    rw [finrank_zero_of_subsingleton, milnorBranchDefect_eq_zero_of_order_one f hf hn]
  | source f e _ ih =>
    have hirr' : Irreducible (e.forward.pullbackRingHom f) :=
      (MulEquiv.irreducible_iff e.pullbackRingEquiv.toMulEquiv).mpr hirr
    obtain ⟨γ, ⟨hinj, hcurve, hnc⟩, hfd, hrank⟩ := ih hirr'
    let γ' := e.forward.comp γ
    have hlin : γ'.pullbackAlgHom.toLinearMap =
        γ.pullbackAlgHom.toLinearMap ∘ₗ e.forward.pullbackAlgHom.toLinearMap := by
      refine LinearMap.ext fun g => ?_
      change (e.forward.comp γ).pullbackRingHom g = γ.pullbackRingHom (e.forward.pullbackRingHom g)
      rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    have hsurj : LinearMap.range e.forward.pullbackAlgHom.toLinearMap = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro g
      obtain ⟨g', hg'⟩ := e.pullbackAlgEquiv.surjective g
      exact ⟨g', hg'⟩
    have himage : γ'.pullbackImage = γ.pullbackImage := by
      rw [PointedMapGerm.pullbackImage, PointedMapGerm.pullbackImage, hlin,
        LinearMap.range_comp_of_range_eq_top _ hsurj]
    refine ⟨γ', ⟨e.forward.comp_hasInjectiveRepresentative γ e.forward_hasInjectiveRepresentative
      hinj, ?_, γ.exists_nonzero_coordinate_pullback_comp_equiv hnc e⟩, ?_, ?_⟩
    · rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
      exact hcurve
    · rw [himage]
      exact hfd
    · rw [himage, hrank, ← milnorBranchDefect_pullback]
  | blowup f m hm horder hnext c hchild ih =>
    let H := pointBlowupTransform c m f horder
    have hHmem : H ∈ maximalIdeal 2 := hchild.mem_maximalIdeal
    have hHunit : ¬ IsUnit (projectiveStrictTransform m f horder (some c)) := by
      rw [projectiveStrictTransform_some]
      intro hu
      exact valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp hHmem)
    obtain ⟨hHirr', hother⟩ := irreducible_projectiveStrictTransform_of_nonunit m (by omega) f
      horder hnext hirr (some c) hHunit
    have hHirr : Irreducible H := by
      rwa [projectiveStrictTransform_some] at hHirr'
    obtain ⟨γ, hγ, hfd, hrank⟩ := ih hHirr
    obtain ⟨hinj, hcurve, hnc⟩ := hγ
    have hreg : IsRegularInFirstCoordinateOfOrder H m := by
      have ho := projectiveExceptionalIntersectionOrder_eq_of_irreducible m (by omega) f horder
        hnext hirr (some c) hHunit
      rw [projectiveExceptionalIntersectionOrder, projectiveStrictTransform_some,
        pointBlowupExceptionalLine_eq_lineGerm] at ho
      change vanishingOrder ((lineGerm (firstCoordinateVector 1)).pullbackRingHom H) = (m : ℕ∞)
      have hne : vanishingOrder ((lineGerm (firstCoordinateVector 1)).pullbackRingHom H) ≠ ⊤ := by
        intro htop
        rw [htop, ENat.toNat_top] at ho
        omega
      rw [← ho, ENat.natCast_toNat hne]
    have hker := parametrization_kernel_eq_span_singleton H hHirr γ hcurve hnc
    have hyne : γ.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0 := by
      intro hz
      have hmem : coordinate (1 : Fin 2) ∈ Ideal.span {H} := by
        rw [← hker]
        exact hz
      have hdvd : H ∣ coordinate (1 : Fin 2) := Ideal.mem_span_singleton.mp hmem
      have haxis := finite_intersection_exceptional_pointBlowupTransform c m f horder hnext
      exact hHirr.not_isUnit (haxis.isUnit_of_common_divisor H hdvd dvd_rfl)
    let γ' := (pointBlowupChartGerm c).comp γ
    have hcurve' : γ'.pullbackRingHom f = 0 := by
      rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, pointBlowupTransform_factor,
        map_mul]
      change _ * γ.pullbackRingHom H = 0
      rw [hcurve, mul_zero]
    have hnc' : ∃ i : Fin 2, γ'.pullbackRingHom (coordinate i) ≠ 0 := by
      refine ⟨1, ?_⟩
      rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
        pointBlowupChartGerm_pullback_one]
      exact hyne
    have himage : γ'.pullbackImage =
        (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap).map
          γ.pullbackAlgHom.toLinearMap := by
      change LinearMap.range γ'.pullbackAlgHom.toLinearMap = _
      rw [← LinearMap.range_comp]
      congr 1
      refine LinearMap.ext fun g => ?_
      change ((pointBlowupChartGerm c).comp γ).pullbackRingHom g =
        γ.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom g)
      rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    have hkerℂ : LinearMap.ker γ.pullbackAlgHom.toLinearMap = (Ideal.span {H}).restrictScalars ℂ :=
      PointedMapGerm.ker_pullbackAlgHom_toLinearMap hHirr ⟨hinj, hcurve, hnc⟩
    obtain ⟨hBfd, hBrank⟩ :=
      finiteDimensional_and_finrank_pointBlowupChart_quotient c m (by omega) H hreg
    obtain ⟨hfd', hrank'⟩ := DeltaLinearAlgebra.finiteDimensional_and_finrank_quotient_map
      γ.pullbackAlgHom.toLinearMap
      (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap) hfd
      (by rw [hkerℂ]; exact hBfd)
    have hD : milnorBranchDefect f = m * (m - 1) + milnorBranchDefect H := by
      have h := projectiveStrictTransform_milnorBranchDefect_recurrence_of_singular_cover
        m (by omega) f horder hnext hirr.squarefree {some c} (by
          intro t ht
          rw [Finset.mem_singleton]
          by_contra hne
          have hmem : projectiveStrictTransform m f horder t ∈ maximalIdeal 2 :=
            Ideal.pow_le_self two_ne_zero ht
          exact valueRingHom_ne_zero_of_isUnit (hother t hne) (mem_maximalIdeal_iff.mp hmem))
      simpa only [Finset.sum_singleton, projectiveStrictTransform_some] using h
    have hrank'' : finrank ℂ (Germ 1 ⧸ γ'.pullbackImage) =
        finrank ℂ (Germ 1 ⧸ γ.pullbackImage) + ∑ k ∈ Finset.range m, k := by
      rw [himage, hrank', hkerℂ, hBrank]
      rfl
    refine ⟨γ', ⟨hinj.pointBlowupChart_comp hyne c, hcurve', hnc'⟩, ?_, ?_⟩
    · rw [himage]
      exact hfd'
    · rw [hrank'', hD, mul_add, hrank, ← Finset.sum_range_id_mul_two]
      ring

end Germ

namespace PointedMapGerm

/-- For every injective parametrization `γ` of an irreducible plane
equation `f`, the quotient `ℂ{t}/γ^* ℂ{x, y}` is finite dimensional and
twice its dimension is the Milnor branch quantity of `f`. -/
theorem finiteDimensional_and_two_mul_finrank_of_irreducible {f : Germ 2} (hf : Irreducible f)
    {γ : PointedMapGerm 1 2} (hγ : γ.IsInjectiveParametrizationOf f) :
    FiniteDimensional ℂ (Germ 1 ⧸ γ.pullbackImage) ∧
      2 * finrank ℂ (Germ 1 ⧸ γ.pullbackImage) = milnorBranchDefect f := by
  obtain ⟨γ₀, hγ₀, hfd, hrank⟩ :=
    (hasFiniteSmoothBlowupChain_of_irreducible f hf).exists_parametrization_two_mul_finrank hf
  obtain ⟨e⟩ := nonempty_quotient_pullbackImage_equiv hf hγ₀ hγ
  exact ⟨e.finiteDimensional, by rw [← e.finrank_eq]; exact hrank⟩

end PointedMapGerm

end OnLeConjecture.Analytic
