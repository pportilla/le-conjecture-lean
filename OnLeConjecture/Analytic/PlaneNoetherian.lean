/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralWeierstrassDivision
public import OnLeConjecture.Analytic.Dimension
public import OnLeConjecture.Analytic.LinearCoordinates
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of the plane analytic germ ring

Every nonzero proper ideal is transported by a linear source change to an
ideal containing a distinguished Weierstrass polynomial. Division makes the
quotient by that polynomial finite over the one variable analytic germ ring.
The quotient is therefore Noetherian, and finite generation lifts across the
principal quotient.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The analytic germ ring in two variables is Noetherian. -/
noncomputable instance instIsNoetherianRingTwo :
    IsNoetherianRing (Germ 2) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro J
  by_cases hJBot : J = ⊥
  · subst J
    exact Submodule.fg_bot
  obtain ⟨f, hfJ, hfZero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJBot
  by_cases hfUnit : IsUnit f
  · have hJTop : J = ⊤ := J.eq_top_of_isUnit_mem hfJ hfUnit
    subst J
    exact Ideal.fg_top (Germ 2)
  obtain ⟨e, n, hregular⟩ :=
    Germ.exists_linear_equiv_regularInFirstCoordinate hfZero
  have hn : 0 < n := by
    by_contra hn
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hunitTransformed :
        IsUnit (e.forward.pullbackRingHom f) := by
      simpa using Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
    apply hfUnit
    exact (MulEquiv.isUnit_map e.pullbackRingEquiv.toMulEquiv).mp (by
      simpa using hunitTransformed)
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let φ : Germ 2 →+* Germ 2 := e.pullbackRingEquiv.toRingHom
  let ψ : Germ 2 →+* Germ 2 := e.pullbackRingEquiv.symm.toRingHom
  let J' : Ideal (Germ 2) := Ideal.map φ J
  let g : Germ 2 := φ f
  have hgRegular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1) := by
    simpa [g, φ, PointedEquivGerm.pullbackRingEquiv_apply] using hregular
  have hgJ : g ∈ J' := by
    exact Ideal.mem_map_of_mem φ hfJ
  obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hgRegular
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  let K : Ideal (Germ 2) := Ideal.span {W}
  have hWJ : W ∈ J' := by
    have hproduct : g * (↑(hu.unit⁻¹) : Germ 2) ∈ J' := by
      simpa [mul_comm] using
        J'.mul_mem_left (↑(hu.unit⁻¹) : Germ 2) hgJ
    have hproductEq : g * (↑(hu.unit⁻¹) : Germ 2) = W := by
      calc
        g * (↑(hu.unit⁻¹) : Germ 2) =
            (W * u) * (↑(hu.unit⁻¹) : Germ 2) := by
          rw [hfactor]
        _ = W * ((↑hu.unit : Germ 2) *
            (↑(hu.unit⁻¹) : Germ 2)) := by
          rw [hu.unit_spec, mul_assoc]
        _ = W := by simp
    rw [hproductEq] at hproduct
    exact hproduct
  have hKJ : K ≤ J' := by
    change Ideal.span {W} ≤ J'
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hWJ
  let _ : Algebra (Germ 1) (Germ 2) :=
    (Germ.hyperplaneExtension 1).toAlgebra
  have hfinite : Module.Finite (Germ 1) (Germ 2 ⧸ K) := by
    simpa [K, W] using
      Germ.quotient_monicPolynomial_moduleFinite
        d P hPMonic hPDegree hPCoeff
  let _ : Module.Finite (Germ 1) (Germ 2 ⧸ K) := hfinite
  let _ : IsNoetherianRing (Germ 2 ⧸ K) :=
    IsNoetherianRing.of_finite (Germ 1) (Germ 2 ⧸ K)
  have hmap : (Ideal.map (Ideal.Quotient.mk K) J').FG :=
    IsNoetherian.noetherian _
  have hKfg : K.FG := by
    exact Submodule.fg_span (Set.finite_singleton W)
  have hinf : J' ⊓ RingHom.ker (Ideal.Quotient.mk K) = K := by
    rw [Ideal.mk_ker, inf_eq_right]
    exact hKJ
  have hinfFg : (J' ⊓ RingHom.ker (Ideal.Quotient.mk K)).FG := by
    rw [hinf]
    exact hKfg
  have hJ' : J'.FG :=
    Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
      hmap hinfFg Ideal.Quotient.mk_surjective
  have hback : (Ideal.map ψ J').FG := hJ'.map ψ
  have hbackEq : Ideal.map ψ J' = J := by
    change Ideal.map ψ (Ideal.map φ J) = J
    rw [Ideal.map_map]
    have hcomp : ψ.comp φ = RingHom.id (Germ 2) := by
      apply DFunLike.ext _ _
      intro x
      change e.pullbackRingEquiv.symm (e.pullbackRingEquiv x) = x
      exact e.pullbackRingEquiv.symm_apply_apply x
    rw [hcomp, Ideal.map_id]
  rwa [hbackEq] at hback

/-- The plane analytic germ ring has Krull dimension two. -/
theorem ringKrullDim_two :
    ringKrullDim (Germ 2) = (2 : ℕ∞) :=
  Germ.ringKrullDim_eq_natCast 2

/-- The plane analytic germ ring is regular. -/
noncomputable instance instIsRegularLocalRingTwo :
    IsRegularLocalRing (Germ 2) :=
  Germ.isRegularLocalRing_of_isNoetherianRing 2

end Germ

end OnLeConjecture.Analytic
