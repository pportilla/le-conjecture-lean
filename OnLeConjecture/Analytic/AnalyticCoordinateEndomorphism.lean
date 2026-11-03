/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteCoordinateGeneration
public import OnLeConjecture.Analytic.MonicTriangularFinite

/-!
# Endomorphisms of analytic germ rings

A local complex algebra endomorphism of an analytic germ ring is determined
by the images of the coordinate germs. Every tuple of analytic germs that
vanishes at the origin is the component tuple of a pointed analytic map germ.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Two complex algebra endomorphisms that preserve the maximal ideal and
agree on the coordinate germs are equal. -/
theorem algHom_ext_of_map_maximalIdeal_le
    {n : ℕ} (phi psi : Germ n →ₐ[ℂ] Germ n)
    (hphi : Ideal.map phi (Germ.maximalIdeal n) ≤
      Germ.maximalIdeal n)
    (hpsi : Ideal.map psi (Germ.maximalIdeal n) ≤
      Germ.maximalIdeal n)
    (hcoordinate : ∀ i : Fin n,
      phi (Germ.coordinate i) = psi (Germ.coordinate i)) :
    phi = psi := by
  apply AlgHom.ext
  intro g
  apply sub_eq_zero.mp
  apply Germ.eq_zero_of_mem_maximalIdeal_pow_all
  intro N
  obtain ⟨p, hp⟩ :=
    Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow n N g
  let q : Germ n := Germ.coordinatePolynomialAlgHom n p
  have hpolynomial : phi q = psi q := by
    let left : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Germ n :=
      phi.comp (Germ.coordinatePolynomialAlgHom n)
    let right : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Germ n :=
      psi.comp (Germ.coordinatePolynomialAlgHom n)
    have hmaps : left = right := by
      apply MvPolynomial.algHom_ext
      intro i
      change phi (Germ.coordinatePolynomialAlgHom n
          (MvPolynomial.X i)) =
        psi (Germ.coordinatePolynomialAlgHom n
          (MvPolynomial.X i))
      rw [Germ.coordinatePolynomialAlgHom_X]
      exact hcoordinate i
    exact AlgHom.congr_fun hmaps p
  have hphiRemainder : phi (g - q) ∈ Germ.maximalIdeal n ^ N := by
    have hmem : phi (g - q) ∈
        Ideal.map phi (Germ.maximalIdeal n ^ N) :=
      Ideal.mem_map_of_mem phi hp
    rw [Ideal.map_pow] at hmem
    exact (pow_le_pow_left' hphi N) hmem
  have hpsiRemainder : psi (g - q) ∈ Germ.maximalIdeal n ^ N := by
    have hmem : psi (g - q) ∈
        Ideal.map psi (Germ.maximalIdeal n ^ N) :=
      Ideal.mem_map_of_mem psi hp
    rw [Ideal.map_pow] at hmem
    exact (pow_le_pow_left' hpsi N) hmem
  have hdifference : phi g - psi g =
      phi (g - q) - psi (g - q) := by
    rw [map_sub, map_sub, hpolynomial]
    abel
  rw [hdifference]
  exact Ideal.sub_mem _ hphiRemainder hpsiRemainder

end Germ

namespace PointedMapGerm

/-- A map germ with an injective representative can be cancelled from the
left against a source endomorphism. -/
theorem HasInjectiveRepresentative.eq_identity_of_comp_eq
    {n m : ℕ} {f : PointedMapGerm n m}
    (hinjective : f.HasInjectiveRepresentative)
    {g : PointedMapGerm n n} (hcomp : f.comp g = f) :
    g = PointedMapGerm.identity n := by
  rcases hinjective with
    ⟨F, hF, hFZero, hf, s, hs, hFInjective⟩
  obtain ⟨G, hG, hGZero, hg⟩ := g.exists_ofFunction
  have hfunctions :
      ((F ∘ G : Source n → Source m) : FunctionMapGerm n m) =
        (F : FunctionMapGerm n m) := by
    have h := congrArg
      (fun q : PointedMapGerm n m => q.1.1) hcomp
    rw [hf, hg, PointedMapGerm.comp_ofFunction] at h
    exact h
  have hequal : ∀ᶠ z in nhds (0 : Source n), F (G z) = F z :=
    Filter.Germ.coe_eq.mp hfunctions
  have hsGZero : s ∈ nhds (G 0) := by
    simpa only [hGZero] using hs
  have hGMem : ∀ᶠ z in nhds (0 : Source n), G z ∈ s :=
    hG.continuousAt.eventually hsGZero
  have hidMem : ∀ᶠ z in nhds (0 : Source n), z ∈ s := hs
  have hidentity : ∀ᶠ z in nhds (0 : Source n), G z = z := by
    filter_upwards [hequal, hGMem, hidMem] with z heq hGz hz
    exact hFInjective hGz hz heq
  rw [hg]
  apply Subtype.ext
  apply Subtype.ext
  exact Filter.Germ.coe_eq.mpr hidentity

/-- A tuple of analytic germs that vanishes at the origin is the component
tuple of a pointed analytic map germ. -/
theorem exists_with_components
    {n m : ℕ} (q : Fin m → Germ n)
    (hq : ∀ i, q i ∈ Germ.maximalIdeal n) :
    ∃ g : PointedMapGerm n m,
      ∀ i, g.1.component i = q i := by
  let Q : Fin m → Source n → ℂ := fun i => Quotient.out (q i).1
  have hQ : ∀ i, AnalyticAt ℂ (Q i) 0 := by
    intro i
    have hi := (q i).2
    change IsAnalyticGerm (q i).1 at hi
    rw [← Quotient.out_eq (q i).1] at hi
    exact (isAnalyticGerm_ofFun (Q i)).mp hi
  let F : Source n → Source m := fun z i => Q i z
  have hF : AnalyticAt ℂ F 0 := by
    rw [analyticAt_pi_iff]
    exact hQ
  have hFZero : F 0 = 0 := by
    funext i
    have hi := (Germ.mem_maximalIdeal_iff.mp (hq i))
    change Filter.Germ.value (q i).1 = 0 at hi
    rw [← Quotient.out_eq (q i).1] at hi
    exact hi
  refine ⟨PointedMapGerm.ofFunction F hF hFZero, fun i => ?_⟩
  apply Subtype.ext
  change ((MapGerm.ofFunction F hF).component i).1 = (q i).1
  rw [MapGerm.component_ofFunction]
  exact Quotient.out_eq (q i).1

/-- Every complex algebra automorphism of an analytic germ ring is induced
by a pointed analytic map germ. -/
theorem exists_pullbackRingHom_eq_algEquiv
    {n : ℕ} (e : Germ n ≃ₐ[ℂ] Germ n) :
    ∃ g : PointedMapGerm n n,
      g.pullbackRingHom = e.toAlgHom.toRingHom := by
  have hcoordinate : ∀ i : Fin n,
      e (Germ.coordinate i) ∈ Germ.maximalIdeal n := by
    intro i
    have hi : e (Germ.coordinate i) ∈
        Ideal.map e.toRingEquiv (Germ.maximalIdeal n) :=
      Ideal.mem_map_of_mem e.toRingEquiv
        (Germ.coordinate_mem_maximalIdeal i)
    rw [Germ.maximalIdeal_eq_isLocalRing,
      IsLocalRing.map_ringEquiv_maximalIdeal,
      ← Germ.maximalIdeal_eq_isLocalRing] at hi
    exact hi
  obtain ⟨g, hg⟩ :=
    PointedMapGerm.exists_with_components
      (fun i => e (Germ.coordinate i)) hcoordinate
  let pullback : Germ n →ₐ[ℂ] Germ n :=
    { __ := g.pullbackRingHom
      commutes' := g.pullback_constRingHom }
  have hpullbackMaximal : Ideal.map pullback
      (Germ.maximalIdeal n) ≤ Germ.maximalIdeal n := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    exact g.pullback_mem_maximalIdeal hq
  have heMaximal : Ideal.map e.toAlgHom
      (Germ.maximalIdeal n) ≤ Germ.maximalIdeal n := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    have hmem : e q ∈
        Ideal.map e.toRingEquiv (Germ.maximalIdeal n) :=
      Ideal.mem_map_of_mem e.toRingEquiv hq
    rw [Germ.maximalIdeal_eq_isLocalRing,
      IsLocalRing.map_ringEquiv_maximalIdeal,
      ← Germ.maximalIdeal_eq_isLocalRing] at hmem
    exact hmem
  have heq : pullback = e.toAlgHom := by
    apply Germ.algHom_ext_of_map_maximalIdeal_le
      pullback e.toAlgHom hpullbackMaximal heMaximal
    intro i
    rw [show pullback (Germ.coordinate i) =
      g.pullbackRingHom (Germ.coordinate i) by rfl,
      g.pullback_coordinate, hg i]
    rfl
  exact ⟨g, congrArg AlgHom.toRingHom heq⟩

end PointedMapGerm

end OnLeConjecture.Analytic
