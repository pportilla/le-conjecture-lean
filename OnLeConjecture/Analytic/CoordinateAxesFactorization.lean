/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import OnLeConjecture.Analytic.PlaneIsolatedFiberElimination
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import OnLeConjecture.Analytic.CoordinatePermutation

/-!
# Factorization from support on the coordinate axes

A nonzero plane analytic germ whose zeros near the origin lie on the two
coordinate axes is a product of coordinate powers and an analytic unit.
The support condition is imposed on an analytic representative, not on its
prime divisors. The proof derives the condition on prime divisors using
isolated zeros in one variable and the impossibility of an isolated zero
for a scalar analytic function of two variables.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

namespace Germ

/-- Every analytic germ has an analytic representative. -/
theorem exists_analytic_representative {n : ℕ} (g : Germ n) :
    ∃ F : Source n → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      g = Germ.ofFunction F hF := by
  rcases g with ⟨g, hg⟩
  induction g using Filter.Germ.inductionOn with
  | _ F => exact ⟨F, (isAnalyticGerm_ofFun F).mp hg, rfl⟩

/-- A nonzero one-variable analytic germ has no zeros other than the origin
in a sufficiently small neighborhood. Its value at the origin need not be
zero. -/
theorem eventually_zero_imp_eq_zero_of_oneVariable_ne_zero
    (F : Source 1 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hne : Germ.ofFunction F hF ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : Source 1), F z = 0 → z = 0 := by
  let e : Source 1 ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have hOne : AnalyticAt ℂ (F ∘ e.symm) 0 := by
    have hF' : AnalyticAt ℂ F (e.symm 0) := by simpa using hF
    exact hF'.comp (e.symm.analyticAt 0)
  have he : Tendsto e (𝓝 (0 : Source 1)) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using
      e.continuous.continuousAt (x := (0 : Source 1))
  rcases hOne.eventually_eq_zero_or_eventually_ne_zero with hzero | hpunct
  · exact (hne (by
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      change ∀ᶠ z in 𝓝 (0 : Source 1), F z = 0
      simpa only [Function.comp_apply, e.symm_apply_apply] using
        he.eventually hzero)).elim
  · have h := he.eventually (eventually_nhdsWithin_iff.mp hpunct)
    filter_upwards [h] with z hz hFz
    by_contra hz0
    have hez : e z ≠ 0 := by simpa using hz0
    exact hz hez (by simpa only [Function.comp_apply, e.symm_apply_apply] using hFz)

/-- A scalar analytic function of two complex variables that vanishes at
the origin cannot have an isolated zero there. -/
theorem not_eventually_zero_imp_eq_zero_of_plane_scalar
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) :
    ¬ (∀ᶠ z in 𝓝 (0 : Source 2), F z = 0 → z = 0) := by
  intro hisolated
  let P : Source 2 → Source 1 := fun z _ ↦ F z
  have hP : AnalyticAt ℂ P 0 := analyticAt_pi_iff.mpr fun _ ↦ hF
  have hP0 : P 0 = 0 := by ext i; exact hF0
  let p : PointedMapGerm 2 1 := PointedMapGerm.ofFunction P hP hP0
  have hpIsolated : p.HasIsolatedZeroRepresentative := by
    refine ⟨P, hP, hP0, rfl, {z | F z = 0 → z = 0}, hisolated, ?_⟩
    intro z hz hzero
    exact hz (congrFun hzero 0)
  have hradical :=
    PointedMapGerm.localAnalyticNullstellensatzAtOrigin_two 1 p hpIsolated
  have hle : Germ.maximalIdeal 2 ≤ p.1.coordinateIdeal.radical := by
    rw [hradical]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Germ.maximalIdeal_fg 2)
  have hcomponent (i : Fin 1) : p.1.component i = Germ.ofFunction F hF := by
    apply Subtype.ext
    exact MapGerm.component_ofFunction P hP i
  have hprincipal : p.1.coordinateIdeal ≤ Ideal.span {Germ.ofFunction F hF} := by
    rw [MapGerm.coordinateIdeal_le]
    intro i
    rw [hcomponent]
    exact Ideal.subset_span (Set.mem_singleton _)
  apply Germ.not_maximalIdeal_pow_le_span_singleton (Germ.ofFunction F hF)
    (by simpa using hF0)
  exact ⟨N, hN.trans hprincipal⟩

/-- If the coordinate `i` does not divide an analytic plane germ, its
restriction to that coordinate axis has isolated zeros. -/
theorem eventually_zero_on_axis_imp_eq_zero_of_coordinate_not_dvd
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0) (i : Fin 2)
    (hnot : ¬ Germ.coordinate i ∣ Germ.ofFunction F hF) :
    ∀ᶠ z in 𝓝 (0 : Source 2), z i = 0 → F z = 0 → z = 0 := by
  let e := coordinateSwapEquiv i
  let G : Source 2 → ℂ := F ∘ e.symm
  have hG : AnalyticAt ℂ G 0 := by
    have hF' : AnalyticAt ℂ F (e.symm 0) := by simpa using hF
    exact hF'.comp (e.symm.analyticAt 0)
  let R : Source 1 → ℂ := G ∘ Germ.hyperplaneInclusion 1
  have hR : AnalyticAt ℂ R 0 := by
    have hG' : AnalyticAt ℂ G (Germ.hyperplaneInclusion 1 0) := by simpa using hG
    exact hG'.comp ((Germ.hyperplaneInclusion 1).analyticAt 0)
  have he : Tendsto e (𝓝 (0 : Source 2)) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using
      e.continuous.continuousAt (x := (0 : Source 2))
  have hRne : Germ.ofFunction R hR ≠ 0 := by
    intro hzero
    have hRzero : R =ᶠ[𝓝 0] fun _ ↦ 0 := by
      exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hzero)
    obtain ⟨Q, hQ, hfactor⟩ :=
      Germ.AnalyticAt.exists_eventuallyEq_coordinate_mul_of_restrict_eq_zero hG hRzero
    have hQe : AnalyticAt ℂ (Q ∘ e) 0 := by
      have hQ' : AnalyticAt ℂ Q (e 0) := by simpa using hQ
      exact hQ'.comp (e.analyticAt 0)
    apply hnot
    refine ⟨Germ.ofFunction (Q ∘ e) hQe, ?_⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    have h := hfactor.comp_tendsto he
    filter_upwards [h] with z hz
    change F z = z i * Q (e z)
    simpa only [G, Function.comp_apply, e.symm_apply_apply, e,
      coordinateSwapEquiv_apply_zero] using hz
  have hRisolated :=
    Germ.eventually_zero_imp_eq_zero_of_oneVariable_ne_zero R hR hRne
  have htail : Tendsto (Germ.hyperplaneTail 1) (𝓝 (0 : Source 2)) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using
      (Germ.hyperplaneTail 1).continuous.continuousAt (x := (0 : Source 2))
  have h := (htail.comp he).eventually hRisolated
  filter_upwards [h] with z hz hzi hFz
  have hez0 : e z 0 = 0 := by simpa only [e, coordinateSwapEquiv_apply_zero] using hzi
  have hprojection : Germ.hyperplaneInclusion 1 (Germ.hyperplaneTail 1 (e z)) = e z := by
    ext j
    induction j using Fin.cases with
    | zero => simpa only [Germ.hyperplaneInclusion_apply_zero] using hez0.symm
    | succ j => simp
  have hRz : R (Germ.hyperplaneTail 1 (e z)) = 0 := by
    change F (e.symm (Germ.hyperplaneInclusion 1 (Germ.hyperplaneTail 1 (e z)))) = 0
    rw [hprojection, e.symm_apply_apply]
    exact hFz
  have hezero : e z = 0 := by
    have htailzero : Germ.hyperplaneTail 1 (e z) = 0 := hz hRz
    rw [← hprojection, htailzero, map_zero]
  exact e.injective (by simpa using hezero)

/-- A prime plane analytic germ whose zeros lie on the coordinate axes is
associated to one of the two coordinate germs. -/
theorem associated_coordinate_of_prime_of_zeros_supported_on_axes
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Prime (Germ.ofFunction P hP))
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2),
      P z = 0 → z 0 = 0 ∨ z 1 = 0) :
    Associated (Germ.ofFunction P hP) (Germ.coordinate 0) ∨
      Associated (Germ.ofFunction P hP) (Germ.coordinate 1) := by
  by_contra hnot
  push Not at hnot
  have hcoordinateNotUnit (i : Fin 2) : ¬ IsUnit (Germ.coordinate i) := by
    rw [Germ.isUnit_iff_valueRingHom_ne_zero, Germ.valueRingHom_coordinate]
    simp
  have hnot0 : ¬ Germ.coordinate 0 ∣ Germ.ofFunction P hP := by
    intro hdiv
    exact hnot.1 ((hp.irreducible.dvd_iff.mp hdiv).resolve_left (hcoordinateNotUnit 0))
  have hnot1 : ¬ Germ.coordinate 1 ∣ Germ.ofFunction P hP := by
    intro hdiv
    exact hnot.2 ((hp.irreducible.dvd_iff.mp hdiv).resolve_left (hcoordinateNotUnit 1))
  have haxis0 :=
    Germ.eventually_zero_on_axis_imp_eq_zero_of_coordinate_not_dvd P hP 0 hnot0
  have haxis1 :=
    Germ.eventually_zero_on_axis_imp_eq_zero_of_coordinate_not_dvd P hP 1 hnot1
  have hP0 : P 0 = 0 := by
    by_contra hnonzero
    exact hp.not_isUnit (Germ.isUnit_of_valueRingHom_ne_zero (by simpa using hnonzero))
  apply Germ.not_eventually_zero_imp_eq_zero_of_plane_scalar P hP hP0
  filter_upwards [hsupport, haxis0, haxis1] with z hz hz0 hz1 hPz
  exact (hz hPz).elim (fun h ↦ hz0 h hPz) (fun h ↦ hz1 h hPz)

/-- The representative-level zero-set condition implies the corresponding
condition on every prime divisor. -/
theorem prime_divisors_associated_coordinate_of_zeros_supported_on_axes
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2),
      F z = 0 → z 0 = 0 ∨ z 1 = 0)
    (p : Germ 2) (hp : Prime p) (hdiv : p ∣ Germ.ofFunction F hF) :
    Associated p (Germ.coordinate 0) ∨ Associated p (Germ.coordinate 1) := by
  obtain ⟨P, hP, rfl⟩ := Germ.exists_analytic_representative p
  obtain ⟨q, hfactor⟩ := hdiv
  obtain ⟨Q, hQ, rfl⟩ := Germ.exists_analytic_representative q
  have hfactorFun : F =ᶠ[𝓝 0] fun z ↦ P z * Q z :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hfactor)
  apply Germ.associated_coordinate_of_prime_of_zeros_supported_on_axes P hP hp
  filter_upwards [hsupport, hfactorFun] with z hz hfactorz hPz
  apply hz
  rw [hfactorz, hPz, zero_mul]

/-- A nonzero analytic plane germ with no zeros off the coordinate axes
near the origin is a product of coordinate powers and an analytic unit. -/
theorem exists_coordinate_factorization_of_zeros_supported_on_axes
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hne : Germ.ofFunction F hF ≠ 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2),
      F z = 0 → z 0 = 0 ∨ z 1 = 0) :
    ∃ a b : ℕ, ∃ u : (Germ 2)ˣ,
      Germ.ofFunction F hF = Germ.coordinate (0 : Fin 2) ^ a *
        Germ.coordinate (1 : Fin 2) ^ b * ↑u := by
  apply Germ.exists_coordinate_factorization_of_prime_divisors (Germ.ofFunction F hF) hne
  exact Germ.prime_divisors_associated_coordinate_of_zeros_supported_on_axes F hF hsupport

/-- The coordinate factorization can be realized by an analytic function
that is nonvanishing on a neighborhood of the origin. -/
theorem exists_eventuallyEq_coordinate_powers_mul_nonvanishing
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hne : Germ.ofFunction F hF ≠ 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2),
      F z = 0 → z 0 = 0 ∨ z 1 = 0) :
    ∃ a b : ℕ, ∃ U : Source 2 → ℂ, AnalyticAt ℂ U 0 ∧
      U 0 ≠ 0 ∧ (∀ᶠ z in 𝓝 (0 : Source 2), U z ≠ 0) ∧
      F =ᶠ[𝓝 0] fun z ↦ z 0 ^ a * z 1 ^ b * U z := by
  obtain ⟨a, b, u, hfactor⟩ :=
    Germ.exists_coordinate_factorization_of_zeros_supported_on_axes F hF hne hsupport
  obtain ⟨U, hU, hu⟩ := Germ.exists_analytic_representative (↑u : Germ 2)
  have hU0 : U 0 ≠ 0 := by
    have h := Germ.valueRingHom_ne_zero_of_isUnit u.isUnit
    simpa only [hu, Germ.valueRingHom_ofFunction] using h
  refine ⟨a, b, U, hU, hU0, hU.continuousAt.eventually_ne hU0, ?_⟩
  rw [hu] at hfactor
  exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hfactor)

end Germ

end OnLeConjecture.Analytic
