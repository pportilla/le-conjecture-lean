/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneSectionSpecialization

/-!
# The critical points on nearby level curves

Let `G` represent a locally injective germ `(ℂ², 0) → (ℂ³, 0)` whose first
component `G₀` is reduced and meets `G₂` finitely. The critical locus of
`G` is the zero set of the reduced common divisor `σ` of the Jacobian
minors, away from the origin. The level curves of `G₀` meet the curve
`σ = 0` transversally at nonzero points near the origin, because `σ` meets
its polar with respect to `G₀` finitely. Conservation of intersection
multiplicities therefore gives a constant number of critical points on
every nearby level curve, namely `i₀(G₀, σ)`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- Two germs vanishing at the origin with invertible Jacobian meet with
multiplicity one. -/
theorem intersectionMultiplicity_eq_one_of_isUnit_jacobian {f ℓ : Germ 2}
    (hf : f ∈ maximalIdeal 2) (hℓ : ℓ ∈ maximalIdeal 2) (hJ : IsUnit (jacobian f ℓ)) :
    ∃ h : HasFiniteIntersection f ℓ, intersectionMultiplicity f ℓ h = 1 := by
  have hpartial : ¬ ∀ i : Fin 2, partialDerivative i f ∈ maximalIdeal 2 := by
    intro hall
    apply isUnit_iff_valueRingHom_ne_zero.mp hJ
    rw [jacobian_eq, map_sub, map_mul, map_mul, mem_maximalIdeal_iff.mp (hall 0),
      mem_maximalIdeal_iff.mp (hall 1)]
    ring
  have hn : f ∉ maximalIdeal 2 ^ 2 := by
    intro hsq
    have hfirst := (mem_firstOrderIdeal_iff.mp ((maximalIdeal_sq_le_firstOrderIdeal 2) hsq)).2
    exact hpartial ((differential_eq_zero_iff_partialDerivatives_mem_maximalIdeal f).mp hfirst)
  have hirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf hn).2
  have hfin : HasFiniteIntersection f ℓ :=
    hasFiniteIntersection_of_hasFiniteIntersection_jacobian hirr.ne_zero
      (hasFiniteIntersection_of_isUnit_right hJ)
  obtain ⟨hpolar, -, heq⟩ := exists_polar_intersection_identity f ℓ hf hℓ hirr.squarefree hfin
  have hpol0 : polarIntersectionMultiplicity f ℓ hpolar = 0 :=
    intersectionMultiplicity_eq_zero_of_isUnit_right f _ hJ hpolar
  have hμ : Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) = 0 := by
    have htop : jacobianIdeal f = ⊤ := by
      push Not at hpartial
      obtain ⟨i, hi⟩ := hpartial
      have hu : IsUnit (partialDerivative i f) := by
        rw [mem_maximalIdeal_iff] at hi
        exact isUnit_of_valueRingHom_ne_zero hi
      apply Ideal.eq_top_of_isUnit_mem _ _ hu
      fin_cases i
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    have : Subsingleton (Germ 2 ⧸ jacobianIdeal f) := by
      rw [htop]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  exact ⟨hfin, by omega⟩

theorem ofFunction_pow {n : ℕ} (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    ofFunction f hf ^ k = ofFunction (fun y => f y ^ k) (hf.pow k) := by
  apply Subtype.ext
  change ((f : FunctionGerm n)) ^ k = ((fun y => f y ^ k : Source n → ℂ) : FunctionGerm n)
  rw [← Filter.Germ.coe_pow]
  rfl

theorem jacobian_germAt_eq (F H : Source 2 → ℂ) (x : Source 2) (hF : AnalyticAt ℂ F x)
    (hH : AnalyticAt ℂ H x) :
    AnalyticAt ℂ (fun y =>
        fderiv ℂ F y (coordinateVector 0) * fderiv ℂ H y (coordinateVector 1) -
        fderiv ℂ F y (coordinateVector 1) * fderiv ℂ H y (coordinateVector 0)) x ∧
      jacobian (germAt F x) (germAt H x) = germAt (fun y =>
        fderiv ℂ F y (coordinateVector 0) * fderiv ℂ H y (coordinateVector 1) -
        fderiv ℂ F y (coordinateVector 1) * fderiv ℂ H y (coordinateVector 0)) x := by
  obtain ⟨hJ, hJeq⟩ := jacobian_ofFunctionAt F H x hF hH
  refine ⟨hJ, ?_⟩
  rw [germAt_eq hF, germAt_eq hH, hJeq, germAt_eq hJ]

namespace CriticalJacobianFactorization

variable {g : PointedMapGerm 2 3} (Dc : CriticalJacobianFactorization g)

/-- The reduced common divisor of the Jacobian minors. -/
noncomputable def reducedDivisor : Germ 2 := ∏ p ∈ Dc.support, p

theorem reducedDivisor_squarefree : Squarefree Dc.reducedDivisor := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply (Dc.irreducible p hp).isRelPrime_iff_not_dvd.mpr
    intro hd
    rcases (Dc.irreducible q hq).dvd_iff.mp hd with hu | hass
    · exact (Dc.irreducible p hp).not_isUnit hu
    · exact Dc.pairwise_not_associated hp hq hpq hass.symm
  · intro p hp
    exact (Dc.irreducible p hp).squarefree

theorem reducedDivisor_dvd_divisor : Dc.reducedDivisor ∣ Dc.divisor := by
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp (Dc.order_pos p hp))

theorem divisor_dvd_reducedDivisor_pow :
    Dc.divisor ∣ Dc.reducedDivisor ^ Dc.maxMultiplicity := by
  rw [reducedDivisor, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  apply pow_dvd_pow
  have h : Dc.order p + 1 ≤ Dc.maxMultiplicity :=
    Finset.le_sup (f := fun p => Dc.order p + 1) hp
  omega

end CriticalJacobianFactorization

/-- **Constant number of critical points on nearby level curves.** Under
the hypotheses of `plane_section_delta_specialization`, there is a number
`N` such that for every sufficiently small radius `r` and every
sufficiently small nonzero `s`, the critical points of `G` on the level
curve `{G₀ = s}` in the ball of radius `r` are exactly `N` points. -/
theorem plane_section_critical_count
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (D : SectionImageFactorization g)
    (haxis : HasFiniteIntersection (g.1.component 0) (g.1.component 2))
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∃ N : ℕ, ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 →
      ∃ Z : Finset (Source 2),
        (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ G x 0 = s ∧
          ¬ Function.Injective (fderiv ℂ G x))) ∧ Z.card = N := by
  classical
  set v : Source 2 → ℂ := fun y => G y 0 with hvdef
  have hv : AnalyticAt ℂ v 0 := (analyticAt_pi_iff.mp hG) 0
  have hv0 : v 0 = 0 := by simp [hvdef, hG0]
  have hvg : ofFunction v hv = g.1.component 0 := by
    rw [hg]
    apply Subtype.ext
    exact (MapGerm.component_ofFunction G hG 0).symm
  have hsq := D.squarefree_component_zero
  have hcomp (j : Fin 3) : g.1.component j ∈ maximalIdeal 2 := by
    rw [← PointedMapGerm.pullback_coordinate]
    exact g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal j)
  obtain ⟨hpolar, -, -⟩ := exists_polar_intersection_identity (g.1.component 0)
    (g.1.component 2) (hcomp 0) (hcomp 2) hsq haxis
  have hJv : HasFiniteIntersection (g.1.component 0)
      (jacobian (g.1.component 0) (g.1.component 2)) := hpolar
  let Dc := g.criticalJacobianFactorization hi
  set σ := Dc.reducedDivisor with hσdef
  obtain ⟨S, hS, hσS⟩ := exists_analyticRepresentative_allOrders σ
  obtain ⟨Q, hQ, hDQ⟩ := exists_analyticRepresentative_allOrders Dc.divisor
  -- finiteness of `v` against the reduced divisor
  have hfinσ : HasFiniteIntersection (ofFunction v hv) (ofFunction S hS) := by
    obtain ⟨a, ha⟩ := Dc.reducedDivisor_dvd_divisor.trans (Dc.divisor_dvd 0 2)
    rw [hvg, ← hσS]
    rw [ha] at hJv
    exact ((hasFiniteIntersection_mul_right_iff _ _ _).mp hJv).1
  -- the zero sets of the divisor and the reduced divisor agree near the origin
  have hzσQ : ∀ᶠ y in 𝓝 (0 : Source 2), S y = 0 → Q y = 0 :=
    eventually_zero_imp_zero_of_dvd S Q hS hQ (hσS ▸ hDQ ▸ Dc.reducedDivisor_dvd_divisor)
  have hzQσ : ∀ᶠ y in 𝓝 (0 : Source 2), Q y = 0 → S y ^ Dc.maxMultiplicity = 0 := by
    apply eventually_zero_imp_zero_of_dvd Q (fun y => S y ^ Dc.maxMultiplicity) hQ (hS.pow _)
    rw [← ofFunction_pow S hS, ← hσS, ← hDQ]
    exact Dc.divisor_dvd_reducedDivisor_pow
  have hcrit := Dc.eventually_critical_iff_divisor_zero G hG hG0 hg Q hQ hDQ
  -- transversality of the level curves to the critical curve
  let T : Source 2 → ℂ := fun y =>
    fderiv ℂ S y (coordinateVector 0) * fderiv ℂ v y (coordinateVector 1) -
      fderiv ℂ S y (coordinateVector 1) * fderiv ℂ v y (coordinateVector 0)
  obtain ⟨hT, hTeq⟩ := jacobian_germAt_eq S v 0 hS hv
  rw [germAt_zero_eq hS, germAt_zero_eq hv] at hTeq
  have hTfin : HasFiniteIntersection (ofFunction S hS) (ofFunction T hT) := by
    have hT' : ofFunction T hT = jacobian (ofFunction S hS) (ofFunction v hv) := by
      rw [hTeq, germAt_zero_eq hT]
    rw [hT']
    by_cases hσu : IsUnit (ofFunction S hS)
    · exact (hasFiniteIntersection_comm _ _).mp (hasFiniteIntersection_of_isUnit_right hσu)
    · have hσm : ofFunction S hS ∈ maximalIdeal 2 := by
        rw [mem_maximalIdeal_iff]
        by_contra hne
        exact hσu (isUnit_of_valueRingHom_ne_zero hne)
      have hvm : ofFunction v hv ∈ maximalIdeal 2 := by rw [hvg]; exact hcomp 0
      obtain ⟨hp, -, -⟩ := exists_polar_intersection_identity _ _ hσm hvm
        (hσS ▸ Dc.reducedDivisor_squarefree) ((hasFiniteIntersection_comm _ _).mp hfinσ)
      exact hp
  have hTzero : ∀ᶠ y in 𝓝 (0 : Source 2), S y = 0 → T y = 0 → y = 0 := by
    let P : Fin 2 → Source 2 → ℂ := ![S, T]
    have hP : ∀ i, AnalyticAt ℂ (P i) 0 := by
      intro i
      fin_cases i
      · exact hS
      · exact hT
    have hspan : Ideal.span (Set.range fun i => ofFunction (P i) (hP i)) =
        pairIdeal (ofFunction S hS) (ofFunction T hT) := by
      rw [pairIdeal_eq_span]
      congr 1
      ext a
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hfinP : Module.Finite ℂ (Germ 2 ⧸
        Ideal.span (Set.range fun i => ofFunction (P i) (hP i))) := by
      rw [hspan]
      exact hTfin
    filter_upwards [eventually_common_zero_imp_eq_zero_of_finite_colength P hP hfinP]
      with y hy hSy hTy
    apply hy
    intro i
    fin_cases i
    · exact hSy
    · exact hTy
  obtain ⟨rσ, hrσ, hcσ⟩ := conservesAlongLevels v S hv hS hv0 hfinσ
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((((hzσQ.and hzQσ).and hcrit).and hTzero).and (hS.eventually_analyticAt.and
      hG.eventually_analyticAt))
  refine ⟨intersectionMultiplicity _ _ hfinσ, min rσ ε, lt_min hrσ hε, fun r hr hrle => ?_⟩
  have hrσ' : r ≤ rσ := hrle.trans (min_le_left _ _)
  have hrε : r ≤ ε := hrle.trans (min_le_right _ _)
  filter_upwards [hcσ r hr hrσ'] with s hs hs0
  obtain ⟨Zσ, hZσ, -, hZσsum⟩ := hs hs0
  have hdata : ∀ x ∈ ball (0 : Source 2) r, v x = s →
      x ≠ 0 ∧ (¬ Function.Injective (fderiv ℂ G x) ↔ S x = 0) := by
    intro x hx hvx
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩ := hεsub (ball_subset_ball hrε hx)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hs0 (hvx.symm.trans hv0)
    refine ⟨hx0, (h3 hx0).trans ⟨fun hQx => ?_, h1⟩⟩
    exact pow_eq_zero_iff (n := Dc.maxMultiplicity) (by
      have := Dc.order_pos
      intro h0
      have hcard := h2 hQx
      rw [h0, pow_zero] at hcard
      exact one_ne_zero hcard) |>.mp (h2 hQx)
  refine ⟨Zσ, ?_, ?_⟩
  · intro x
    rw [hZσ x]
    constructor
    · rintro ⟨hx, hvx, hSx⟩
      exact ⟨hx, hvx, ((hdata x hx hvx).2).mpr hSx⟩
    · rintro ⟨hx, hvx, hni⟩
      exact ⟨hx, hvx, ((hdata x hx hvx).2).mp hni⟩
  · rw [← hZσsum, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro x hxZ
    obtain ⟨hx, hvx, hSx⟩ := (hZσ x).mp hxZ
    obtain ⟨⟨-, hTx⟩, hSan, hGan⟩ := hεsub (ball_subset_ball hrε hx)
    have hx0 := (hdata x hx hvx).1
    have hvan : AnalyticAt ℂ (fun y => v y - s) x :=
      ((analyticAt_pi_iff.mp hGan) 0).sub analyticAt_const
    obtain ⟨hJx, hJxeq⟩ := jacobian_germAt_eq S (fun y => v y - s) x hSan hvan
    have hTxne : T x ≠ 0 := fun h0 => hx0 (hTx hSx h0)
    have hJunit : IsUnit (jacobian (germAt S x) (germAt (fun y => v y - s) x)) := by
      rw [hJxeq]
      apply isUnit_germAt hJx
      simp only [fderiv_sub_const]
      exact hTxne
    have hSm : germAt S x ∈ maximalIdeal 2 := by
      rw [germAt_eq hSan, mem_maximalIdeal_iff, valueRingHom_ofFunctionAt]
      exact hSx
    have hvm : germAt (fun y => v y - s) x ∈ maximalIdeal 2 := by
      rw [germAt_eq hvan, mem_maximalIdeal_iff, valueRingHom_ofFunctionAt]
      simp [hvx]
    obtain ⟨hfin1, hone⟩ := intersectionMultiplicity_eq_one_of_isUnit_jacobian hSm hvm hJunit
    rw [localIntersection_comm, localIntersection_eq hfin1, hone]

/-- At a smooth point of a level curve, the local delta invariant is
positive exactly at the critical points of `G`. -/
theorem localSectionDelta_pos_iff (G : Source 2 → Source 3) (x : Source 2)
    (hG : AnalyticAt ℂ G x) (S : Set (Source 2)) (hS : S ∈ 𝓝 x) (hinj : InjOn G S)
    (hsmooth : ∃ z : Source 2, fderiv ℂ G x z 0 ≠ 0) :
    0 < localSectionDelta G x ↔ ¬ Function.Injective (fderiv ℂ G x) := by
  obtain ⟨D, hirr, -, -, hsm, -⟩ := exists_recentered_section_image_delta G x hG S hS hinj hsmooth
  rw [localSectionDelta_eq G x hG
    (PointedMapGerm.recenter_hasInjectiveRepresentative G x hG S hS hinj) D, ← hsm,
    Nat.pos_iff_ne_zero, not_not]
  constructor
  · intro hne
    by_contra hn
    exact hne (deltaInvariant_eq_zero_of_order_one (irreducible_mem_maximalIdeal _ hirr) hn)
  · intro hm h0
    exact not_mem_maximalIdeal_sq_of_deltaInvariant_eq_zero hirr h0 hm

/-- The restriction of an injective continuous map to a level set in a
closed ball is a closed embedding. -/
theorem isClosedEmbedding_restrict_level (G : Source 2 → Source 3) (r : ℝ) (s : ℂ)
    (hGc : ContinuousOn G (closedBall 0 r)) (hinj : InjOn G (closedBall 0 r)) :
    Topology.IsClosedEmbedding
      ((closedBall (0 : Source 2) r ∩ (fun x => G x 0) ⁻¹' {s}).domRestrict G) := by
  set K := closedBall (0 : Source 2) r ∩ (fun x => G x 0) ⁻¹' {s} with hKdef
  have hc0 : ContinuousOn (fun x => G x 0) (closedBall 0 r) :=
    (continuous_apply 0).comp_continuousOn hGc
  have hK : IsClosed K := hc0.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hKc : IsCompact K := (isCompact_closedBall 0 r).of_isClosed_subset hK inter_subset_left
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  apply Continuous.isClosedEmbedding
  · exact (hGc.mono inter_subset_left).domRestrict
  · intro a b hab
    exact Subtype.ext (hinj a.2.1 b.2.1 hab)

/-- **Specialization of plane sections.** Let `g : (ℂ², 0) → (ℂ³, 0)` be
locally injective with analytic representative `G`, let the section
`V₀ = {g₀ = 0}` be reduced (encoded by the factorization `D`, whose reduced
image equation defines `W₀`), and let `g₀` meet `g₂` finitely. There is a
number `N`, positive when `dg = 0` and zero when `dg` is injective, such that
for every sufficiently small radius `r` and every sufficiently small nonzero
`s` the following hold.
* `G` is injective on the ball of radius `r`, the level curve
  `V_s = {G₀ = s}` is smooth in that ball, and the restriction of `G` to
  `V_s ∩ closedBall 0 r` is a closed embedding.
* The critical points of `G` on `V_s` in the ball form a set `Z` with exactly
  `N` elements.
* At every point `x` of `V_s` in the ball, the image of `V_s` near `G(x)` is
  the zero set of an irreducible reduced equation in the plane `{x₀ = s}`,
  whose delta invariant is `localSectionDelta G x`. This equation is singular
  exactly when `x ∈ Z`.
* `δ(W₀) = δ(V₀) + ∑_{x ∈ Z} δ(W_s, G(x))`. -/
theorem plane_section_specialization
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (D : SectionImageFactorization g)
    (haxis : HasFiniteIntersection (g.1.component 0) (g.1.component 2))
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∃ N : ℕ, (g.differential = 0 → 0 < N) ∧ (Function.Injective g.differential → N = 0) ∧
      ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 →
        ∃ Z : Finset (Source 2),
          (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ G x 0 = s ∧
            ¬ Function.Injective (fderiv ℂ G x))) ∧
          Z.card = N ∧
          InjOn G (ball (0 : Source 2) r) ∧
          Topology.IsClosedEmbedding
            ((closedBall (0 : Source 2) r ∩ (fun x => G x 0) ⁻¹' {s}).domRestrict G) ∧
          (∀ x ∈ ball (0 : Source 2) r, G x 0 = s →
            fderiv ℂ (fun y => G y 0) x ≠ 0 ∧
            ∃ (hGx : AnalyticAt ℂ G x)
              (Dx : SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hGx)),
              Irreducible Dx.imageEquation ∧
              (Dx.imageEquation ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z) ∧
              localSectionDelta G x = deltaInvariant Dx.imageEquation ∧
              (0 < localSectionDelta G x ↔ x ∈ Z) ∧
              ∀ (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0), Dx.imageEquation = ofFunction W hW →
                ∀ T ∈ 𝓝 (0 : Source 2), ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : Source 2) ρ ⊆ T ∧
                  ∀ᶠ y in 𝓝 (0 : Source 2), W y = 0 ↔
                    ∃ z ∈ closedBall (0 : Source 2) ρ,
                      G (x + z) - G x = hyperplaneInclusion 2 y) ∧
          deltaInvariant D.imageEquation =
            deltaInvariant (g.1.component 0) + ∑ x ∈ Z, localSectionDelta G x := by
  classical
  obtain ⟨r₁, hr₁, h₁⟩ := plane_section_delta_specialization g hi D haxis G hG hG0 hg
  obtain ⟨N, r₂, hr₂, h₂⟩ := plane_section_critical_count g hi D haxis G hG hG0 hg
  have hi' := hi
  obtain ⟨G', hG', hG'0, hgG', S₀, hS₀, hinj₀⟩ := hi'
  have hGG' : G =ᶠ[𝓝 0] G' :=
    Filter.Germ.coe_eq.mp (congrArg (fun p => p.1.1) (hg.symm.trans hgG'))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hS₀ hGG') hG.eventually_analyticAt)
  have hinjε : InjOn G (ball (0 : Source 2) ε) := by
    intro a ha b hb hab
    obtain ⟨⟨ha₀, ha'⟩, -⟩ := hεsub ha
    obtain ⟨⟨hb₀, hb'⟩, -⟩ := hεsub hb
    apply hinj₀ ha₀ hb₀
    change G a = G' a at ha'
    change G b = G' b at hb'
    rw [← ha', ← hb', hab]
  have hpos : g.differential = 0 → 0 < N := by
    intro h0
    have hlt := D.deltaInvariant_lt_of_differential_eq_zero hi h0
    have hev := (h₁ (min r₁ r₂) (lt_min hr₁ hr₂) (min_le_left _ _)).and
      (h₂ (min r₁ r₂) (lt_min hr₁ hr₂) (min_le_right _ _))
    have hev' : ∀ᶠ s in 𝓝[≠] (0 : ℂ), _ := hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨s, ⟨hs₁, hs₂⟩, hs0⟩ := (hev'.and self_mem_nhdsWithin).exists
    obtain ⟨Z₁, hZ₁, -, hδ⟩ := hs₁ hs0
    obtain ⟨Z₂, hZ₂, hcard⟩ := hs₂ hs0
    have hZ : Z₁ = Z₂ := Finset.ext fun x => (hZ₁ x).trans (hZ₂ x).symm
    rw [← hcard, ← hZ, Nat.pos_iff_ne_zero]
    intro hc
    rw [Finset.card_eq_zero.mp hc, Finset.sum_empty, add_zero] at hδ
    omega
  have hzero : Function.Injective g.differential → N = 0 := by
    intro hinjd
    have hnlt : ¬ deltaInvariant (g.1.component 0) < deltaInvariant D.imageEquation :=
      fun h => ((D.deltaInvariant_lt_iff_not_injective_differential hi).mp h) hinjd
    set r' := min (min r₁ r₂) (ε / 2) with hr'def
    have hr'pos : 0 < r' := lt_min (lt_min hr₁ hr₂) (half_pos hε)
    have hr'ε : r' ≤ ε := (min_le_right _ _).trans (half_le_self hε.le)
    have hev := (h₁ r' hr'pos ((min_le_left _ _).trans (min_le_left _ _))).and
      (h₂ r' hr'pos ((min_le_left _ _).trans (min_le_right _ _)))
    have hev' : ∀ᶠ s in 𝓝[≠] (0 : ℂ), _ := hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨s, ⟨hs₁, hs₂⟩, hs0⟩ := (hev'.and self_mem_nhdsWithin).exists
    obtain ⟨Z₁, hZ₁, hsmooth, hδ⟩ := hs₁ hs0
    obtain ⟨Z₂, hZ₂, hcard⟩ := hs₂ hs0
    have hZ : Z₁ = Z₂ := Finset.ext fun x => (hZ₁ x).trans (hZ₂ x).symm
    have hsum0 : ∑ x ∈ Z₁, localSectionDelta G x = 0 := by omega
    have hZempty : Z₁ = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hxb, hvx, hni⟩ := (hZ₁ x).mp hx
      have hGx : AnalyticAt ℂ G x := (hεsub (ball_subset_ball hr'ε hxb)).2
      have hd := hsmooth x hxb hvx
      have hsm : ∃ z : Source 2, fderiv ℂ G x z 0 ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hd
        ext z
        rw [fderiv_component_apply hGx.differentiableAt]
        exact hall z
      have hlpos := (localSectionDelta_pos_iff G x hGx _ (isOpen_ball.mem_nhds hxb)
        (hinjε.mono (ball_subset_ball hr'ε)) hsm).mpr hni
      have hle := Finset.single_le_sum (f := fun x => localSectionDelta G x)
        (fun _ _ => Nat.zero_le _) hx
      omega
    rw [← hcard, ← hZ, hZempty, Finset.card_empty]
  refine ⟨N, hpos, hzero, min (min r₁ r₂) (ε / 2), lt_min (lt_min hr₁ hr₂) (half_pos hε),
    fun r hr hrle => ?_⟩
  have hr₁' : r ≤ r₁ := hrle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₂' : r ≤ r₂ := hrle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrε2 : r ≤ ε / 2 := hrle.trans (min_le_right _ _)
  have hrε : r ≤ ε := hrε2.trans (half_le_self hε.le)
  have hcl : closedBall (0 : Source 2) r ⊆ ball (0 : Source 2) ε :=
    closedBall_subset_ball (lt_of_le_of_lt hrε2 (half_lt_self hε))
  filter_upwards [h₁ r hr hr₁', h₂ r hr hr₂'] with s hs₁ hs₂ hs0
  obtain ⟨Z₁, hZ₁, hsmooth, hδ⟩ := hs₁ hs0
  obtain ⟨Z₂, hZ₂, hcard⟩ := hs₂ hs0
  have hZ : Z₁ = Z₂ := Finset.ext fun x => (hZ₁ x).trans (hZ₂ x).symm
  have hinjr : InjOn G (ball (0 : Source 2) r) := hinjε.mono (ball_subset_ball hrε)
  have hemb := isClosedEmbedding_restrict_level G r s
    (fun x hx => ((hεsub (hcl hx)).2).continuousAt.continuousWithinAt) (hinjε.mono hcl)
  refine ⟨Z₁, hZ₁, hZ ▸ hcard, hinjr, hemb, ?_, hδ⟩
  intro x hx hvx
  have hd := hsmooth x hx hvx
  have hGx : AnalyticAt ℂ G x := (hεsub (ball_subset_ball hrε hx)).2
  have hsm : ∃ z : Source 2, fderiv ℂ G x z 0 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hd
    ext z
    rw [fderiv_component_apply hGx.differentiableAt]
    exact hall z
  have hball : ball (0 : Source 2) r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  obtain ⟨Dx, hirr, -, -, hsmIff, himage⟩ :=
    exists_recentered_section_image_delta G x hGx _ hball hinjr hsm
  have hsing : Dx.imageEquation ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z₁ := by
    rw [hZ₁]
    constructor
    · intro hm
      exact ⟨hx, hvx, fun hinjx => hsmIff.mpr hinjx hm⟩
    · rintro ⟨-, -, hni⟩
      by_contra hn
      exact hni (hsmIff.mp hn)
  refine ⟨hd, hGx, Dx, hirr, hsing,
    localSectionDelta_eq G x hGx
      (PointedMapGerm.recenter_hasInjectiveRepresentative G x hGx _ hball hinjr) Dx, ?_, himage⟩
  rw [localSectionDelta_pos_iff G x hGx _ hball hinjr hsm, hZ₁]
  exact ⟨fun h => ⟨hx, hvx, h⟩, fun h => h.2.2⟩

end OnLeConjecture.Analytic
