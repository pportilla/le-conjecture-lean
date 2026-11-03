/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralWeierstrassDivision
public import OnLeConjecture.Analytic.OneVariableColength

/-!
# Elimination from a plane analytic ideal

An ideal containing a germ regular in the first coordinate has finite
colength exactly when its contraction to the one variable parameter ring is
nonzero. Weierstrass preparation and division prove the algebraic part of
this elimination criterion.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

noncomputable local instance : Algebra (Germ 1) (Germ 2) :=
  (Germ.hyperplaneExtension 1).toAlgebra

/-- The extension of the one variable coordinate is the second plane
coordinate. -/
theorem hyperplaneExtension_coordinate_plane :
    Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [Germ.hyperplaneExtension, PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  change
    ((MapGerm.ofFunction (Germ.hyperplaneTail 1)
      ((Germ.hyperplaneTail 1).analyticAt 0)).component 0).1 =
      (Germ.coordinate (1 : Fin 2)).1
  rw [MapGerm.component_ofFunction]
  rfl

/-- Passing from a quotient by a smaller ideal to a quotient by a larger
ideal preserves module finiteness over the parameter ring. -/
theorem quotient_moduleFinite_of_le {I K : Ideal (Germ 2)}
    (hKI : K ≤ I)
    (hfinite : Module.Finite (Germ 1) (Germ 2 ⧸ K)) :
    Module.Finite (Germ 1) (Germ 2 ⧸ I) := by
  let _ : Module.Finite (Germ 1) (Germ 2 ⧸ K) := hfinite
  let quotientMap : (Germ 2 ⧸ K) →ₐ[Germ 1] (Germ 2 ⧸ I) :=
    Ideal.quotientMapₐ I (AlgHom.id (Germ 1) (Germ 2)) hKI
  apply Module.Finite.of_surjective quotientMap.toLinearMap
  intro q
  rcases Ideal.Quotient.mk_surjective q with ⟨g, rfl⟩
  refine ⟨Ideal.Quotient.mk K g, ?_⟩
  exact Ideal.quotient_map_mkₐ I
    (AlgHom.id (Germ 1) (Germ 2)) hKI

/-- An equivalence of complex algebras preserves finite dimensionality of
quotients by corresponding ideals. -/
theorem quotient_moduleFinite_iff_of_map_eq
    (I J : Ideal (Germ 2)) (e : Germ 2 ≃ₐ[ℂ] Germ 2)
    (hIJ : Ideal.map e.toRingEquiv.toRingHom I = J) :
    Module.Finite ℂ (Germ 2 ⧸ I) ↔
      Module.Finite ℂ (Germ 2 ⧸ J) := by
  let quotientEquiv : (Germ 2 ⧸ I) ≃ₐ[ℂ] Germ 2 ⧸ J :=
    Ideal.quotientEquivAlg I J e hIJ.symm
  constructor
  · intro hfinite
    let _ : Module.Finite ℂ (Germ 2 ⧸ I) := hfinite
    exact Module.Finite.equiv quotientEquiv.toLinearEquiv
  · intro hfinite
    let _ : Module.Finite ℂ (Germ 2 ⧸ J) := hfinite
    exact Module.Finite.equiv quotientEquiv.symm.toLinearEquiv

/-- A quotient finite over the parameter ring is finite dimensional over
the complex numbers when a nonzero parameter germ annihilates it. -/
theorem quotient_moduleFinite_of_parameter_mem
    (I : Ideal (Germ 2)) {r : Germ 1} (hr : r ≠ 0)
    (hrI : Germ.hyperplaneExtension 1 r ∈ I)
    (hfinite : Module.Finite (Germ 1) (Germ 2 ⧸ I)) :
    Module.Finite ℂ (Germ 2 ⧸ I) := by
  let _ : Module.Finite (Germ 1) (Germ 2 ⧸ I) := hfinite
  let extensionAlgHom : Germ 1 →ₐ[ℂ] Germ 2 :=
    { Germ.hyperplaneExtension 1 with
      commutes' := fun c ↦ by
        change Germ.hyperplaneExtension 1 (Germ.constRingHom 1 c) =
          Germ.constRingHom 2 c
        exact PointedMapGerm.pullback_constRingHom
          (Germ.hyperplaneTailGerm 1) c }
  let extensionQuotientAlgHom : Germ 1 →ₐ[ℂ] (Germ 2 ⧸ I) :=
    (Ideal.Quotient.mkₐ ℂ I).comp extensionAlgHom
  have hspan : ∀ q ∈ Ideal.span ({r} : Set (Germ 1)),
      extensionQuotientAlgHom q = 0 := by
    intro q hq
    rw [Ideal.mem_span_singleton] at hq
    rcases hq with ⟨a, rfl⟩
    rw [map_mul]
    change Ideal.Quotient.mk I (Germ.hyperplaneExtension 1 r) * _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hrI, zero_mul]
  let quotientAlgHom :
      (Germ 1 ⧸ Ideal.span {r}) →ₐ[ℂ] (Germ 2 ⧸ I) :=
    Ideal.Quotient.liftₐ (Ideal.span {r}) extensionQuotientAlgHom hspan
  let _ : Algebra (Germ 1 ⧸ Ideal.span {r}) (Germ 2 ⧸ I) :=
    quotientAlgHom.toRingHom.toAlgebra
  let _ : IsScalarTower ℂ (Germ 1 ⧸ Ideal.span {r})
      (Germ 2 ⧸ I) :=
    IsScalarTower.of_algebraMap_eq (R := ℂ)
      (S := Germ 1 ⧸ Ideal.span {r}) (A := Germ 2 ⧸ I)
      fun c ↦ (quotientAlgHom.commutes c).symm
  let _ : IsScalarTower (Germ 1) (Germ 1 ⧸ Ideal.span {r})
      (Germ 2 ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun q ↦ by
      change Ideal.Quotient.mk I (Germ.hyperplaneExtension 1 q) =
        quotientAlgHom (Ideal.Quotient.mk (Ideal.span {r}) q)
      exact (Ideal.Quotient.lift_mk (Ideal.span {r})
        extensionQuotientAlgHom.toRingHom hspan).symm
  let _ : Module.Finite ℂ (Germ 1 ⧸ Ideal.span {r}) :=
    Germ.quotient_span_moduleFinite hr
  let _ : Module.Finite (Germ 1 ⧸ Ideal.span {r}) (Germ 2 ⧸ I) :=
    Module.Finite.of_restrictScalars_finite (Germ 1)
      (Germ 1 ⧸ Ideal.span {r}) (Germ 2 ⧸ I)
  exact Module.Finite.trans (Germ 1 ⧸ Ideal.span {r}) (Germ 2 ⧸ I)

/-- A regular element of a plane ideal makes its quotient finite over the
one variable parameter ring. -/
theorem quotient_moduleFinite_over_parameter_of_regular_mem
    (I : Ideal (Germ 2)) {g : Germ 2} {d : ℕ}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1))
    (hgI : g ∈ I) :
    Module.Finite (Germ 1) (Germ 2 ⧸ I) := by
  obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hregular
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  let K : Ideal (Germ 2) := Ideal.span {W}
  have hWI : W ∈ I := by
    have hproduct : g * (↑(hu.unit⁻¹) : Germ 2) ∈ I := by
      simpa [mul_comm] using
        I.mul_mem_left (↑(hu.unit⁻¹) : Germ 2) hgI
    have hproductEq : g * (↑(hu.unit⁻¹) : Germ 2) = W := by
      calc
        g * (↑(hu.unit⁻¹) : Germ 2) =
            (W * u) * (↑(hu.unit⁻¹) : Germ 2) := by
          rw [hfactor]
        _ = W * ((↑hu.unit : Germ 2) *
            (↑(hu.unit⁻¹) : Germ 2)) := by
          rw [hu.unit_spec, mul_assoc]
        _ = W := by simp
    rwa [hproductEq] at hproduct
  have hKI : K ≤ I := by
    change Ideal.span {W} ≤ I
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hWI
  have hfiniteK : Module.Finite (Germ 1) (Germ 2 ⧸ K) := by
    simpa [K, W] using
      Germ.quotient_monicPolynomial_moduleFinite
        d P hPMonic hPDegree hPCoeff
  exact Germ.quotient_moduleFinite_of_le hKI hfiniteK

/-- If a plane ideal contains a regular element and a nonzero parameter
germ, then it has finite complex colength. -/
theorem quotient_moduleFinite_of_regular_mem_and_parameter_mem
    (I : Ideal (Germ 2)) {g : Germ 2} {d : ℕ}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1))
    (hgI : g ∈ I) {r : Germ 1} (hr : r ≠ 0)
    (hrI : Germ.hyperplaneExtension 1 r ∈ I) :
    Module.Finite ℂ (Germ 2 ⧸ I) := by
  apply Germ.quotient_moduleFinite_of_parameter_mem I hr hrI
  exact Germ.quotient_moduleFinite_over_parameter_of_regular_mem
    I hregular hgI

/-- Under a regularity hypothesis, finite colength is equivalent to the
existence of a nonzero germ in the one variable elimination ideal. -/
theorem quotient_moduleFinite_iff_exists_parameter_mem_of_regular_mem
    (I : Ideal (Germ 2)) {g : Germ 2} {d : ℕ}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1))
    (hgI : g ∈ I) :
    Module.Finite ℂ (Germ 2 ⧸ I) ↔
      ∃ r : Germ 1, r ≠ 0 ∧ Germ.hyperplaneExtension 1 r ∈ I := by
  constructor
  · intro hfinite
    obtain ⟨N, hN⟩ :=
      (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le I).mp
        hfinite
    refine ⟨Germ.coordinate (0 : Fin 1) ^ N,
      pow_ne_zero N Germ.coordinate_zero_ne_zero, ?_⟩
    rw [map_pow, Germ.hyperplaneExtension_coordinate_plane]
    exact hN (Ideal.pow_mem_pow
      (Germ.coordinate_mem_maximalIdeal (1 : Fin 2)) N)
  · rintro ⟨r, hr, hrI⟩
    exact Germ.quotient_moduleFinite_of_regular_mem_and_parameter_mem
      I hregular hgI hr hrI

/-- Under a regularity hypothesis, a plane ideal has finite colength exactly
when its contraction to the parameter ring is nonzero. -/
theorem quotient_moduleFinite_iff_comap_hyperplaneExtension_ne_bot
    (I : Ideal (Germ 2)) {g : Germ 2} {d : ℕ}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1))
    (hgI : g ∈ I) :
    Module.Finite ℂ (Germ 2 ⧸ I) ↔
      Ideal.comap (Germ.hyperplaneExtension 1) I ≠ ⊥ := by
  rw [Germ.quotient_moduleFinite_iff_exists_parameter_mem_of_regular_mem
    I hregular hgI]
  constructor
  · rintro ⟨r, hr, hrI⟩ hbot
    have hrComap : r ∈
        Ideal.comap (Germ.hyperplaneExtension 1) I := hrI
    have hrZero : r = 0 := by
      simpa only [hbot, Ideal.mem_bot] using hrComap
    exact hr hrZero
  · intro hne
    obtain ⟨r, hrComap, hr⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨r, hr, hrComap⟩

end Germ

namespace PointedMapGerm

/-- When one component is regular in the first source coordinate, finite
coordinate fibre is equivalent to nonvanishing of the parameter elimination
ideal. -/
theorem hasFiniteCoordinateFiber_iff_comap_hyperplaneExtension_ne_bot
    {m : ℕ} (f : PointedMapGerm 2 m) {i : Fin m} {d : ℕ}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      (f.1.component i) (d + 1)) :
    Module.Finite ℂ (Germ 2 ⧸ f.1.coordinateIdeal) ↔
      Ideal.comap (Germ.hyperplaneExtension 1) f.1.coordinateIdeal ≠ ⊥ := by
  exact Germ.quotient_moduleFinite_iff_comap_hyperplaneExtension_ne_bot
    f.1.coordinateIdeal hregular (f.1.component_mem_coordinateIdeal i)

end PointedMapGerm

end OnLeConjecture.Analytic
