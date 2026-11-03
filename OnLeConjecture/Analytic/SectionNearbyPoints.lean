/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionSpecializationCore
public import OnLeConjecture.Analytic.SourceConservation
public import OnLeConjecture.Analytic.FinitePrincipalImage
public import OnLeConjecture.Analytic.CriticalDivisorZeroSet
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.Main

/-!
# The central polar identity at nearby points

Let `G` be an analytic representative of a locally injective germ
`(ℂ², 0) → (ℂ³, 0)` and let `F` represent a generator of its surface
equations. At a point `x` near the origin, the germ of `F` at `G(x)` again
generates the equations of the recentred germ of `G`, provided the
pulled back polar `∂₁F ∘ G` does not vanish identically near `x`. The
proof combines the image description of the zero set of `F`, injectivity
of `G` on a compact ball, and Rückert's Nullstellensatz: a non-reduced
factor of `F` at `G(x)` would force `∂₁F ∘ G` to vanish near `x`.

The central polar identity then holds at every such point `x`, for the
recentred germ of `G` and the global functions `J = J(G₀, G₂)` and
`P = ∂₁F ∘ G`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- The Jacobian of the section coordinate and the second target coordinate. -/
noncomputable def sectionJacobian (G : Source 2 → Source 3) (y : Source 2) : ℂ :=
  fderiv ℂ (fun z => G z 0) y (coordinateVector 0) *
      fderiv ℂ (fun z => G z 2) y (coordinateVector 1) -
    fderiv ℂ (fun z => G z 0) y (coordinateVector 1) *
      fderiv ℂ (fun z => G z 2) y (coordinateVector 0)

/-- The pullback along `G` of the first-coordinate partial derivative of `F`. -/
noncomputable def surfacePolar (F : Source 3 → ℂ) (G : Source 2 → Source 3) (y : Source 2) : ℂ :=
  fderiv ℂ F (G y) (coordinateVector 1)

theorem recenter_component_eq_germAt {m : ℕ} (G : Source 2 → Source m) (x : Source 2)
    (hG : AnalyticAt ℂ G x) (j : Fin m) :
    (PointedMapGerm.recenterOfFunction G x hG).1.component j =
      germAt (fun y => G y j - G x j) x := by
  have hGj : AnalyticAt ℂ (fun y => G y j - G x j) x :=
    ((analyticAt_pi_iff.mp hG) j).sub analyticAt_const
  rw [germAt_eq hGj]
  apply Subtype.ext
  rfl

theorem recenter_jacobian_eq_germAt (G : Source 2 → Source 3) (x : Source 2)
    (hG : AnalyticAt ℂ G x) :
    jacobian ((PointedMapGerm.recenterOfFunction G x hG).1.component 0)
        ((PointedMapGerm.recenterOfFunction G x hG).1.component 2) =
      germAt (sectionJacobian G) x := by
  obtain ⟨hJ, hJeq⟩ := PointedMapGerm.jacobian_recenterOfFunction_components G x hG 0 2
  rw [hJeq, germAt_eq (show AnalyticAt ℂ (sectionJacobian G) x from hJ)]
  rfl

theorem analyticAt_surfacePolar {F : Source 3 → ℂ} {G : Source 2 → Source 3} {x : Source 2}
    (hG : AnalyticAt ℂ G x) (hF : AnalyticAt ℂ F (G x)) :
    AnalyticAt ℂ (surfacePolar F G) x := by
  have hD : AnalyticAt ℂ (fun y => fderiv ℂ F y (coordinateVector 1)) (G x) :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector 1)).analyticAt _).comp hF.fderiv
  exact hD.comp hG

theorem recenter_pullback_partial_eq_germAt (F : Source 3 → ℂ) (G : Source 2 → Source 3)
    (x : Source 2) (hG : AnalyticAt ℂ G x) (hF : AnalyticAt ℂ F (G x)) :
    (PointedMapGerm.recenterOfFunction G x hG).pullbackRingHom
        (partialDerivative (1 : Fin 3) (ofFunctionAt F (G x) hF)) =
      germAt (surfacePolar F G) x := by
  have hD : AnalyticAt ℂ (fun y => fderiv ℂ F y (coordinateVector 1)) (G x) :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector 1)).analyticAt _).comp hF.fderiv
  rw [partialDerivative_ofFunctionAt, germAt_eq (analyticAt_surfacePolar hG hF)]
  exact recenter_pullback_ofFunctionAt G x hG _ hD

/-- **Equations at nearby points.** Suppose that `G` is continuous and
injective on a closed ball, that every zero of `F` in an open set `W` is an
image point of the ball, and that `F ∘ G` vanishes on the ball. At a point
`x` of the open ball with `G(x) ∈ W`, the germ of `F` at `G(x)` generates
all equations of the recentred germ of `G`, provided the recentred
pullback of `∂₁F` is nonzero. -/
theorem ker_recenter_eq_span_of_pullback_partial_ne_zero
    (G : Source 2 → Source 3) (F : Source 3 → ℂ) (r : ℝ)
    (hGc : ContinuousOn G (closedBall 0 r)) (hinj : InjOn G (closedBall 0 r))
    (hFG : ∀ x' ∈ closedBall (0 : Source 2) r, F (G x') = 0)
    (W : Set (Source 3))
    (hWzero : ∀ y ∈ W, F y = 0 → ∃ x' ∈ closedBall (0 : Source 2) r, G x' = y)
    (x : Source 2) (hx : x ∈ ball (0 : Source 2) r) (hGx : AnalyticAt ℂ G x)
    (hxW : W ∈ 𝓝 (G x)) (hFx : AnalyticAt ℂ F (G x))
    (hP : (PointedMapGerm.recenterOfFunction G x hGx).pullbackRingHom
        (partialDerivative (1 : Fin 3) (ofFunctionAt F (G x) hFx)) ≠ 0) :
    RingHom.ker (PointedMapGerm.recenterOfFunction G x hGx).pullbackRingHom =
      Ideal.span {ofFunctionAt F (G x) hFx} := by
  classical
  let := Germ.uniqueFactorizationMonoid_all 3
  set gx := PointedMapGerm.recenterOfFunction G x hGx with hgx
  set q := G x with hq
  have hballx : ball (0 : Source 2) r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hinjx : gx.HasInjectiveRepresentative :=
    PointedMapGerm.recenter_hasInjectiveRepresentative G x hGx _ hballx
      (hinj.mono ball_subset_closedBall)
  obtain ⟨f, hfirr, -, hkerf⟩ :=
    gx.exists_irreducible_generator_of_finite (gx.injective_isFiniteAtOrigin_two hinjx)
  have htrans : Tendsto (fun z : Source 2 => x + z) (𝓝 0) (𝓝 x) := by
    have h : Continuous (fun z : Source 2 => x + z) := continuous_const.add continuous_id
    simpa using h.tendsto 0
  have hFq0 : gx.pullbackRingHom (ofFunctionAt F q hFx) = 0 := by
    rw [hgx, recenter_pullback_ofFunctionAt]
    rw [show (0 : Germ 2) = ofFunction (fun _ => (0 : ℂ)) analyticAt_const from rfl]
    apply ofFunction_eq_of_eventuallyEq
    filter_upwards [htrans.eventually hballx] with z hz
    exact hFG _ (ball_subset_closedBall hz)
  have hmem : ofFunctionAt F q hFx ∈ RingHom.ker gx.pullbackRingHom := hFq0
  rw [hkerf, Ideal.mem_span_singleton] at hmem
  obtain ⟨h, hh⟩ := hmem
  suffices hu : IsUnit h by
    rw [hkerf, Ideal.span_singleton_eq_span_singleton]
    exact ⟨hu.unit, by rw [hh, IsUnit.unit_spec]⟩
  by_contra hnu
  have hf0 : gx.pullbackRingHom f = 0 := by
    rw [← RingHom.mem_ker, hkerf]
    exact Ideal.subset_span rfl
  have hcontra : f ∣ h → False := by
    rintro ⟨h', rfl⟩
    apply hP
    rw [hh, partialDerivative_mul, partialDerivative_mul]
    simp only [map_add, map_mul, hf0, zero_mul, mul_zero, add_zero]
  by_cases h0 : h = 0
  · exact hcontra (h0 ▸ dvd_zero f)
  apply hcontra
  obtain ⟨Fx, hFxan, rfl⟩ := exists_analyticRepresentative_allOrders f
  obtain ⟨H, hHan, rfl⟩ := exists_analyticRepresentative_allOrders h
  have heqF : ∀ᶠ y in 𝓝 (0 : Source 3), F (q + y) = Fx y * H y :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hh)
  have hFxG : ∀ᶠ x' in 𝓝 x, Fx (G x' - q) = 0 := by
    have hz : gx.pullbackRingHom (ofFunction Fx hFxan) = 0 := hf0
    rw [hgx, PointedMapGerm.pullbackRingHom_apply, PointedMapGerm.recenterOfFunction,
      compPointed_ofFunction] at hz
    have hev : ∀ᶠ z in 𝓝 (0 : Source 2), Fx (G (x + z) - G x) = 0 :=
      Filter.Germ.coe_eq.mp (congrArg Subtype.val hz)
    have hsub : Tendsto (fun x' : Source 2 => x' - x) (𝓝 x) (𝓝 0) := by
      have h : Continuous (fun x' : Source 2 => x' - x) := continuous_id.sub continuous_const
      simpa using h.tendsto x
    filter_upwards [hsub.eventually hev] with x' hx'
    simpa only [add_sub_cancel] using hx'
  obtain ⟨O, hOsub, hO, hxO⟩ := _root_.mem_nhds_iff.mp hFxG
  set K := closedBall (0 : Source 2) r \ O with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 r).diff hO
  have hGK : IsCompact (G '' K) := hKc.image_of_continuousOn (hGc.mono sdiff_subset)
  have hqK : q ∉ G '' K := by
    rintro ⟨x'', ⟨hx''b, hx''O⟩, hx''q⟩
    have := hinj hx''b (ball_subset_closedBall hx) hx''q
    exact hx''O (this ▸ hxO)
  have hnhdsK : (G '' K)ᶜ ∈ 𝓝 q := hGK.isClosed.isOpen_compl.mem_nhds hqK
  have hshift : Tendsto (fun y : Source 3 => q + y) (𝓝 0) (𝓝 q) := by
    have h : Continuous (fun y : Source 3 => q + y) := continuous_const.add continuous_id
    simpa using h.tendsto 0
  have hzero : ∀ᶠ y in 𝓝 (0 : Source 3), (∀ _i : Fin 1, H y = 0) → Fx y = 0 := by
    filter_upwards [heqF, hshift.eventually hxW, hshift.eventually hnhdsK]
      with y hy hyW hyK hHy
    have hFy : F (q + y) = 0 := by rw [hy, hHy 0, mul_zero]
    obtain ⟨x', hx'b, hx'y⟩ := hWzero _ hyW hFy
    have hx'O : x' ∈ O := by
      by_contra hn
      exact hyK ⟨x', ⟨hx'b, hn⟩, hx'y⟩
    have := hOsub hx'O
    change Fx (G x' - q) = 0 at this
    rwa [hx'y, add_sub_cancel_left] at this
  obtain ⟨N, hN, K', hK'an, hK'eq⟩ :=
    LocalComplexGeometry.localAnalyticNullstellensatz_core (f := fun _ : Fin 1 => H)
      (fun _ => hHan) hFxan hzero
  have hdvd : ofFunction H hHan ∣ ofFunction Fx hFxan ^ N := by
    refine ⟨ofFunction (K' 0) (hK'an 0), ?_⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hK'eq] with y hy
    simp only [Fin.sum_univ_one] at hy
    change Fx y ^ N = H y * K' 0 y
    rw [hy, mul_comm]
  obtain ⟨z, hz, hzh⟩ := WfDvdMonoid.exists_irreducible_factor hnu h0
  have hzf : z ∣ ofFunction Fx hFxan := hz.prime.dvd_of_dvd_pow (hzh.trans hdvd)
  rcases hfirr.dvd_iff.mp hzf with hzu | hass
  · exact (hz.not_isUnit hzu).elim
  · exact hass.dvd.trans hzh

/-- The chain rule along a parametrized zero fibre, with the first
coordinate. -/
theorem Germ.pullback_second_partial_mul_derivative_eq_neg_jacobian_mul_derivative
    (γ : PointedMapGerm 1 2) (f g : Germ 2) (hf : γ.pullbackRingHom f = 0) :
    γ.pullbackRingHom (partialDerivative (1 : Fin 2) f) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom g) =
      -(γ.pullbackRingHom (jacobian f g) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (0 : Fin 2)))) := by
  have hchain (h : Germ 2) : partialDerivative (0 : Fin 1) (γ.pullbackRingHom h) =
      γ.pullbackRingHom (partialDerivative (0 : Fin 2) h) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (0 : Fin 2))) +
      γ.pullbackRingHom (partialDerivative (1 : Fin 2) h) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (1 : Fin 2))) := by
    change partialDerivative (0 : Fin 1) (compPointed h γ) = _
    rw [partialDerivative_compPointed_sum, Fin.sum_univ_two,
      PointedMapGerm.pullback_coordinate, PointedMapGerm.pullback_coordinate]
    rfl
  have hfc := hchain f
  rw [hf, partialDerivative_zero] at hfc
  rw [hchain g, jacobian_eq, map_sub, map_mul, map_mul]
  linear_combination -(γ.pullbackRingHom (partialDerivative (1 : Fin 2) g)) * hfc

/-- A germ meeting its polar with respect to `ℓ` finitely meets `ℓ`
finitely. -/
theorem hasFiniteIntersection_of_hasFiniteIntersection_jacobian {f ℓ : Germ 2} (hf : f ≠ 0)
    (hJ : HasFiniteIntersection f (jacobian f ℓ)) : HasFiniteIntersection f ℓ := by
  apply hasFiniteIntersection_of_no_common_prime_divisor _ _ hf
  rintro p hp ⟨hpf, hpℓ⟩
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible p hp.irreducible
  have hzero (h : Germ 2) (hph : p ∣ h) : P.map.pullbackRingHom h = 0 := by
    obtain ⟨a, rfl⟩ := hph
    rw [map_mul, P.curve_eq_zero, zero_mul]
  have hJne := P.pullback_ne_zero _ (hJ.of_dvd_left hpf)
  have h1 := pullback_first_partial_mul_derivative_eq_jacobian_mul_derivative P.map f ℓ
    (hzero f hpf)
  have h2 := Germ.pullback_second_partial_mul_derivative_eq_neg_jacobian_mul_derivative P.map f ℓ
    (hzero f hpf)
  rw [hzero ℓ hpℓ, partialDerivative_zero, mul_zero] at h1 h2
  obtain ⟨i, hi⟩ := P.nonconstant
  have hd := (derivative_ne_zero_and_order_add_one _
    (P.map.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i)) hi).1
  fin_cases i
  · exact mul_ne_zero hJne hd (neg_eq_zero.mp h2.symm)
  · exact mul_ne_zero hJne hd h1.symm

theorem germAt_zero_eq {n : ℕ} {f : Source n → ℂ} (hf : AnalyticAt ℂ f 0) :
    germAt f 0 = ofFunction f hf := by
  have hf' : AnalyticAt ℂ f 0 := hf
  rw [germAt_eq hf']
  apply ofFunction_eq_of_eventuallyEq
  filter_upwards with z
  rw [zero_add]

/-- A reduced plane equation has no critical points near the origin other
than the origin. -/
theorem eventually_fderiv_ne_zero_of_squarefree_of_ne (v : Source 2 → ℂ)
    (hv : AnalyticAt ℂ v 0) (hv0 : v 0 = 0) (hsq : Squarefree (ofFunction v hv)) :
    ∀ᶠ z in 𝓝 (0 : Source 2), z ≠ 0 → fderiv ℂ v z ≠ 0 := by
  have hvm : ofFunction v hv ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, valueRingHom_ofFunction]
    exact hv0
  have hJ := hasFiniteJacobianAlgebra_of_squarefree _ hvm hsq
  let P : Fin 2 → Source 2 → ℂ := fun i y => fderiv ℂ v y (coordinateVector i)
  have hP (i : Fin 2) : AnalyticAt ℂ (P i) 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector i)).analyticAt _).comp hv.fderiv
  have hgerm (i : Fin 2) : ofFunction (P i) (hP i) = partialDerivative i (ofFunction v hv) := by
    rw [← germAt_zero_eq hv, germAt_eq hv, partialDerivative_ofFunctionAt]
    exact ((germAt_eq (hP i)).symm.trans (germAt_zero_eq (hP i))).symm
  have hspan : Ideal.span (Set.range fun i => ofFunction (P i) (hP i)) =
      jacobianIdeal (ofFunction v hv) := by
    rw [jacobianIdeal, pairIdeal_eq_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      dsimp only
      rw [hgerm i]
      fin_cases i
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    · rw [Ideal.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact Ideal.subset_span ⟨0, hgerm 0⟩
      · exact Ideal.subset_span ⟨1, hgerm 1⟩
  have hfin :
      Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range fun i => ofFunction (P i) (hP i))) := by
    rw [hspan]
    exact hJ
  filter_upwards [eventually_common_zero_imp_eq_zero_of_finite_colength P hP hfin] with z hz hz0 hfd
  apply hz0
  apply hz
  intro i
  change fderiv ℂ v z (coordinateVector i) = 0
  rw [hfd]
  rfl

/-- **The polar identity at a point.** If the germ of `F` at `G(x)` generates
the equations of the recentred germ of `G`, then for every reduced section
image factorization `D` of that germ,
`2 δ(w_x) + i_x(G₀ - G₀(x), J) = 2 δ(G₀ - G₀(x)) + i_x(G₀ - G₀(x), ∂₁F ∘ G)`. -/
theorem local_polar_identity (G : Source 2 → Source 3) (F : Source 3 → ℂ) (x : Source 2)
    (hGx : AnalyticAt ℂ G x) (hFx : AnalyticAt ℂ F (G x))
    (hinj : (PointedMapGerm.recenterOfFunction G x hGx).HasInjectiveRepresentative)
    (hker : RingHom.ker (PointedMapGerm.recenterOfFunction G x hGx).pullbackRingHom =
      Ideal.span {ofFunctionAt F (G x) hFx})
    (D : SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hGx))
    (haxis : HasFiniteIntersection (germAt (fun y => G y 0 - G x 0) x)
      (germAt (fun y => G y 2 - G x 2) x)) :
    HasFiniteIntersection (germAt (fun y => G y 0 - G x 0) x) (germAt (sectionJacobian G) x) ∧
      HasFiniteIntersection (germAt (fun y => G y 0 - G x 0) x)
        (germAt (surfacePolar F G) x) ∧
      2 * deltaInvariant D.imageEquation +
          localIntersection (fun y => G y 0 - G x 0) (sectionJacobian G) x =
        2 * deltaInvariant (germAt (fun y => G y 0 - G x 0) x) +
          localIntersection (fun y => G y 0 - G x 0) (surfacePolar F G) x := by
  have h0 := recenter_component_eq_germAt G x hGx 0
  have h2 := recenter_component_eq_germAt G x hGx 2
  have hJ := recenter_jacobian_eq_germAt G x hGx
  have hPd := recenter_pullback_partial_eq_germAt F G x hGx hFx
  rw [← h0, ← h2] at haxis
  obtain ⟨hJf, hPf, heq⟩ := D.two_mul_deltaInvariant_add_polar_eq hinj _ hker haxis
  refine ⟨?_, ?_, ?_⟩
  · rw [← h0, ← hJ]
    exact hJf
  · rw [← h0, ← hPd]
    exact hPf
  · unfold localIntersection
    rw [← h0, ← hJ, ← hPd]
    exact heq

namespace SectionImageFactorization

/-- The delta invariant of the reduced section image does not depend on the
chosen factorization. -/
theorem deltaInvariant_imageEquation_eq {g : PointedMapGerm 2 3}
    (D D' : SectionImageFactorization g) (hg : g.HasInjectiveRepresentative) :
    deltaInvariant D.imageEquation = deltaInvariant D'.imageEquation := by
  have h1 : D.imageEquation ∣ D'.imageEquation :=
    (D.imageEquation_dvd_iff hg _).mpr ((D'.imageEquation_dvd_iff hg _).mp dvd_rfl)
  have h2 : D'.imageEquation ∣ D.imageEquation :=
    (D'.imageEquation_dvd_iff hg _).mpr ((D.imageEquation_dvd_iff hg _).mp dvd_rfl)
  have hass := associated_of_dvd_dvd h1 h2
  have hD := two_mul_deltaInvariant (D.imageEquation_squarefree hg)
  have hD' := two_mul_deltaInvariant (D'.imageEquation_squarefree hg)
  rw [milnorBranchDefect_eq_of_associated (D.imageEquation_squarefree hg) hass] at hD
  omega

end SectionImageFactorization

/-- The delta invariant at `G(x)` of the image of the level curve of `G₀`
through `x`, computed from a reduced section image factorization of the
recentred germ, and zero when no such factorization exists. -/
noncomputable def localSectionDelta (G : Source 2 → Source 3) (x : Source 2) : ℕ := by
  classical
  exact if h : ∃ hG : AnalyticAt ℂ G x,
      Nonempty (SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) then
    deltaInvariant (Classical.choice h.choose_spec).imageEquation
  else 0

theorem localSectionDelta_eq (G : Source 2 → Source 3) (x : Source 2) (hG : AnalyticAt ℂ G x)
    (hinj : (PointedMapGerm.recenterOfFunction G x hG).HasInjectiveRepresentative)
    (D : SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) :
    localSectionDelta G x = deltaInvariant D.imageEquation := by
  classical
  have h : ∃ hG : AnalyticAt ℂ G x,
      Nonempty (SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) :=
    ⟨hG, ⟨D⟩⟩
  unfold localSectionDelta
  rw [dif_pos h]
  exact SectionImageFactorization.deltaInvariant_imageEquation_eq _ D hinj

end OnLeConjecture.Analytic
