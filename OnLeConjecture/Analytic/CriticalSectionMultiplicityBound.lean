/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FixedTransverseSectionOrder
public import OnLeConjecture.Analytic.CriticalDivisorZeroSet
public import OnLeConjecture.Analytic.CriticalSupportNonempty
public import OnLeConjecture.Analytic.CriticalJacobianTargetSpan
public import OnLeConjecture.Analytic.CurveImage
public import OnLeConjecture.Analytic.SectionNearbyPoints

/-!
# Multiplicities of the image germs at nearby critical points

Let `G` represent a locally injective germ `(ℂ², 0) → (ℂ³, 0)` whose first
component is reduced. Every critical point `x ≠ 0` of `G` near the origin lies
on an irreducible component `p` of the common divisor of the Jacobian minors.
The level curve of the first component through `x` is transverse to that
component, and the transverse-section theorem gives an injective
parametrization of the image of this level curve near `G(x)`, whose
irreducible equation has exact multiplicity `order p + 1`. Hence this
multiplicity `a` satisfies `2 ≤ a ≤ maxMultiplicity`.

The equation of the transverse image branch is associated to the reduced
image equation of every section image factorization of the recentred germ.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

theorem coordinateSwapEquiv_zero_apply (z : Source 3) : coordinateSwapEquiv (0 : Fin 3) z = z := by
  funext j
  change (Equiv.piCongrLeft (fun _ : Fin 3 ↦ ℂ) (Equiv.swap 0 0)) z j = z j
  simp

/-- Swapping coordinate zero with itself does not change a map germ. -/
theorem coordinateSwapPointedEquiv_zero_comp {l : ℕ} (R : PointedMapGerm l 3) :
    (coordinateSwapPointedEquiv (0 : Fin 3)).forward.comp R = R := by
  apply PointedMapGerm.ext_components
  intro j
  rw [PointedMapGerm.component_comp_eq_pullback]
  have hj : (coordinateSwapPointedEquiv (0 : Fin 3)).forward.1.component j =
      Germ.coordinate j := by
    simp only [coordinateSwapPointedEquiv, Germ.pointedEquivGermOfContinuousLinearEquiv]
    apply Subtype.ext
    change ((MapGerm.ofFunction (coordinateSwapEquiv (0 : Fin 3))
      ((coordinateSwapEquiv (0 : Fin 3)).analyticAt 0)).component j).1 = (Germ.coordinate j).1
    rw [MapGerm.component_ofFunction, Germ.coe_coordinate]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [coordinateSwapEquiv_zero_apply]
  rw [hj, PointedMapGerm.pullback_coordinate]

/-- The equation of a transverse image branch of the zero level of the first
component is associated to the reduced image equation of every section
image factorization. -/
theorem associated_imageEquation_of_transverse_parametrization
    {R : PointedMapGerm 2 3} (hR : R.HasInjectiveRepresentative)
    (D : SectionImageFactorization R) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom (R.1.component 0) = coordinate 0)
    (P : Germ 2) (hPm : P ∈ maximalIdeal 2) (hep : e.forward.pullbackRingHom P = coordinate 1)
    (β : PointedMapGerm 1 2)
    (hβ : (hyperplaneInclusionGerm 2).comp β =
      R.comp (e.forward.comp (hyperplaneInclusionGerm 1)))
    (w : Germ 2) (hw : RingHom.ker β.pullbackRingHom = Ideal.span {w}) :
    Associated w D.imageEquation := by
  set c := e.forward.comp (hyperplaneInclusionGerm 1) with hc
  have hcpull (y : Germ 2) :
      c.pullbackRingHom y = hyperplaneRestriction 1 (e.forward.pullbackRingHom y) := by
    rw [hc, PointedMapGerm.pullbackRingHom_comp]
    rfl
  have hβq (q : Germ 2) :
      β.pullbackRingHom q = c.pullbackRingHom (R.pullbackRingHom (hyperplaneExtension 2 q)) := by
    have h := congrArg (fun φ : PointedMapGerm 1 3 => φ.pullbackRingHom (hyperplaneExtension 2 q))
      hβ
    simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
    rw [← h]
    change _ = β.pullbackRingHom (hyperplaneRestriction 2 (hyperplaneExtension 2 q))
    rw [hyperplaneRestriction_extension]
  have hc0 : c.pullbackRingHom (R.1.component 0) = 0 := by
    rw [hcpull, he, hyperplaneRestriction_coordinate_zero]
  have hcP : c.pullbackRingHom P = coordinate (0 : Fin 1) := by
    rw [hcpull, hep]
    simpa using hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1)
  have hnc : ∃ i : Fin 2, c.pullbackRingHom (coordinate i) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hle : maximalIdeal 2 ≤ RingHom.ker c.pullbackRingHom := by
      rw [← span_range_coordinate_eq_maximalIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hall i
    have hP0 := hle hPm
    rw [RingHom.mem_ker, hcP] at hP0
    exact coordinate_zero_ne_zero hP0
  have hRm : R.1.component 0 ∈ maximalIdeal 2 :=
    R.coordinateIdeal_le_maximalIdeal (R.1.component_mem_coordinateIdeal 0)
  have hRn : R.1.component 0 ∉ maximalIdeal 2 ^ 2 := by
    intro hsq
    have h := e.forward.pullback_mem_maximalIdeal_pow hsq
    rw [he] at h
    have hd := (mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 h)).2
    have hv := congrArg (fun L : Source 2 →L[ℂ] ℂ => L (coordinateVector 0)) hd
    simp [coordinateVector] at hv
  have hRirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _ hRm hRn).2
  have hkerc := parametrization_kernel_eq_span_singleton _ hRirr c hc0 hnc
  have hiff (q : Germ 2) : w ∣ q ↔ D.imageEquation ∣ q := by
    rw [← Ideal.mem_span_singleton, ← hw, RingHom.mem_ker, hβq, ← RingHom.mem_ker, hkerc,
      Ideal.mem_span_singleton, D.imageEquation_dvd_iff hR]
  exact associated_of_dvd_dvd ((hiff _).mpr dvd_rfl) ((hiff _).mp dvd_rfl)

/-- **Nearby critical points carry transverse image branches of bounded
multiplicity.** Let `G` represent a locally injective germ `f` with reduced
first component. Near the origin, every critical point `x ≠ 0` of `G` has a
transverse injective parametrization `β` of the image of the level curve of
`G₀` through `x`, whose irreducible equation `w` has exact multiplicity `a`
with `2 ≤ a ≤ maxMultiplicity`. -/
theorem eventually_critical_transverse_image_equation
    (f : PointedMapGerm 2 3) (hi : f.HasInjectiveRepresentative)
    (hsq : Squarefree (f.1.component 0))
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : f = PointedMapGerm.ofFunction G hG hG0) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → ¬ Function.Injective (fderiv ℂ G x) →
      ∃ (hGx : AnalyticAt ℂ G x) (e : PointedEquivGerm 2) (P : Germ 2)
        (β : PointedMapGerm 1 2) (w : Germ 2) (a : ℕ),
        P ∈ maximalIdeal 2 ∧
        e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction G x hGx).1.component 0) =
          coordinate 0 ∧
        e.forward.pullbackRingHom P = coordinate 1 ∧
        (hyperplaneInclusionGerm 2).comp β =
          (PointedMapGerm.recenterOfFunction G x hGx).comp
            (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
        β.HasInjectiveRepresentative ∧ Irreducible w ∧
        RingHom.ker β.pullbackRingHom = Ideal.span {w} ∧
        w ∈ maximalIdeal 2 ^ a ∧ w ∉ maximalIdeal 2 ^ (a + 1) ∧
        2 ≤ a ∧ a ≤ (f.criticalJacobianFactorization hi).maxMultiplicity := by
  classical
  set Dc := f.criticalJacobianFactorization hi with hDc
  -- an injective neighbourhood for `G`
  have hi' := hi
  obtain ⟨G₁, hG₁, hG₁0, hg₁, S₁, hS₁, hinj₁⟩ := hi'
  have hGG₁ : G =ᶠ[𝓝 0] G₁ :=
    Filter.Germ.coe_eq.mp (congrArg (fun p => p.1.1) (hg.symm.trans hg₁))
  have hS : S₁ ∩ {y | G y = G₁ y} ∈ 𝓝 (0 : Source 2) := inter_mem hS₁ hGG₁
  have hinj : InjOn G (S₁ ∩ {y | G y = G₁ y}) := by
    intro a ha b hb hab
    apply hinj₁ ha.1 hb.1
    rw [← ha.2, ← hb.2, hab]
  -- the transverse data along each critical branch
  have hbranch (p : Dc.support) : ∃ (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0),
      (p : Germ 2) = ofFunction P hP ∧
      ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → P x = 0 →
        ∃ (hGx : AnalyticAt ℂ G x) (e : PointedEquivGerm 2) (P' : Germ 2)
          (β : PointedMapGerm 1 2) (w : Germ 2),
          P' ∈ maximalIdeal 2 ∧
          e.forward.pullbackRingHom
              ((PointedMapGerm.recenterOfFunction G x hGx).1.component 0) = coordinate 0 ∧
          e.forward.pullbackRingHom P' = coordinate 1 ∧
          (hyperplaneInclusionGerm 2).comp β =
            (PointedMapGerm.recenterOfFunction G x hGx).comp
              (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
          β.HasInjectiveRepresentative ∧ Irreducible w ∧
          RingHom.ker β.pullbackRingHom = Ideal.span {w} ∧
          w ∈ maximalIdeal 2 ^ (Dc.order p + 1) ∧
          w ∉ maximalIdeal 2 ^ (Dc.order p + 1 + 1) := by
    have hp := p.2
    obtain ⟨P, hP, hpP⟩ := exists_analyticRepresentative_allOrders (p : Germ 2)
    obtain ⟨γ, hγinj, hγn, hker⟩ :=
      exists_injective_parametrization_with_kernel_of_irreducible _ (Dc.irreducible _ hp)
    obtain ⟨C, hC, hC0, hγC, SC, hSC, hinjC⟩ := hγinj
    subst hγC
    have hdiv (a b : Fin 3) : ofFunction P hP ^ Dc.order p ∣
        jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component a)
          ((PointedMapGerm.ofFunction G hG hG0).1.component b) := by
      rw [← hpP, ← hg]
      exact Dc.pow_dvd_minors _ hp a b
    have hexact : ∃ a b : Fin 3, ¬ ofFunction P hP ^ (Dc.order p + 1) ∣
        jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component a)
          ((PointedMapGerm.ofFunction G hG hG0).1.component b) := by
      by_contra! h
      have hle := (Dc.order_maximal _ hp (Dc.order p + 1)).mp
        (by simpa only [hpP, hg] using h)
      omega
    have hnot : ¬ ofFunction P hP ∣ (PointedMapGerm.ofFunction G hG hG0).1.component 0 := by
      rw [← hpP, ← hg]
      exact Dc.not_dvd_squarefree_component hi _ hp 0 hsq
    have hker' : ∀ h : Germ 2,
        (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ ofFunction P hP ∣ h := by
      intro h
      rw [← hpP]
      exact hker h
    have hirrP : Irreducible (ofFunction P hP) := hpP ▸ Dc.irreducible _ hp
    have ht := eventually_fixed_transverse_section_of_exact_common_power
      G hG hG0 _ hS hinj P hP hirrP (Dc.order p) hdiv hexact C hC hC0 hker' 0 hnot
    obtain ⟨ρ, hρ, hρsub, -, -, -, hzero⟩ :=
      exists_curve_closedBall_image_eq_zero_set C hC hC0 hγn P hP hker'
        (SC ∩ {t | t ≠ 0 → _}) (inter_mem hSC ht) (hinjC.mono inter_subset_left)
    refine ⟨P, hP, hpP, ?_⟩
    filter_upwards [hzero] with x hx hx0 hPx
    obtain ⟨t, htρ, rfl⟩ := hx.mp hPx
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hx0 hC0
    obtain ⟨hGt, hPt, e, β, hP0, he, hep, hβ, hβinj, horder⟩ := (hρsub htρ).2 ht0
    obtain ⟨w, hwirr, -, hwker, hwm, hwn⟩ :=
      β.exists_irreducible_image_equation_of_order hβinj (Dc.order p + 1) horder
    refine ⟨hGt, e, ofFunctionAt P (C t) hPt, β, w, ?_, he, hep, ?_, hβinj, hwirr, hwker,
      hwm, hwn⟩
    · rw [mem_maximalIdeal_iff, valueRingHom_ofFunctionAt]
      exact hP0
    · rw [hβ, coordinateSwapPointedEquiv_zero_comp]
  choose Pf hPf hpPf hev using hbranch
  -- the critical locus is the zero set of the product of the branch equations
  let Q : Source 2 → ℂ := fun x => ∏ p : Dc.support, Pf p x ^ Dc.order p
  have hQ : AnalyticAt ℂ Q 0 :=
    Finset.analyticAt_fun_prod _ fun p _ => (hPf p).pow _
  have hDQ : Dc.divisor = ofFunction Q hQ := by
    have hprod : Dc.divisor = ∏ p : Dc.support, (p : Germ 2) ^ Dc.order p := by
      rw [CriticalJacobianFactorization.divisor, ← Finset.prod_coe_sort]
    rw [hprod]
    apply Subtype.ext
    change (Germ 2).subtype (∏ p : Dc.support, (p : Germ 2) ^ Dc.order p) =
      (Germ 2).subtype (ofFunction Q hQ)
    rw [map_prod]
    have hterm (p : Dc.support) : (Germ 2).subtype ((p : Germ 2) ^ Dc.order p) =
        Filter.Germ.coeRingHom (𝓝 (0 : Source 2)) (fun x => Pf p x ^ Dc.order p) := by
      rw [map_pow, show (Germ 2).subtype (p : Germ 2) = ((Pf p : Source 2 → ℂ) : FunctionGerm 2)
        from by rw [hpPf p]; rfl]
      rw [← Filter.Germ.coe_pow]
      rfl
    simp only [hterm]
    rw [← map_prod]
    change ((∏ p : Dc.support, fun x => Pf p x ^ Dc.order p : Source 2 → ℂ) : FunctionGerm 2) =
      ((Q : Source 2 → ℂ) : FunctionGerm 2)
    congr 1
    funext x
    simp [Q, Finset.prod_apply]
  have hcrit := Dc.eventually_critical_iff_divisor_zero G hG hG0 hg Q hQ hDQ
  filter_upwards [hcrit, Filter.eventually_all.mpr hev] with x hcx hb hx0 hni
  have hQx : Q x = 0 := (hcx hx0).mp hni
  obtain ⟨p, -, hp0⟩ := Finset.prod_eq_zero_iff.mp hQx
  have hPx : Pf p x = 0 := pow_eq_zero_iff'.mp hp0 |>.1
  obtain ⟨hGx, e, P', β, w, hP'm, he, hep, hβ, hβinj, hwirr, hwker, hwm, hwn⟩ :=
    hb p hx0 hPx
  refine ⟨hGx, e, P', β, w, Dc.order p + 1, hP'm, he, hep, hβ, hβinj, hwirr, hwker, hwm, hwn,
    ?_, ?_⟩
  · have := Dc.order_pos _ p.2
    omega
  · exact Finset.le_sup (f := fun p => Dc.order p + 1) p.2

end OnLeConjecture.Analytic
