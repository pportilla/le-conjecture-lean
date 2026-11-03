/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteColength
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Polynomial coordinate germs

This file embeds the polynomial ring in the ring of complex analytic germs by
evaluating each variable at the corresponding coordinate germ.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Evaluation of a polynomial at the coordinate germs. -/
@[expose] noncomputable def coordinatePolynomialAlgHom (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Germ n :=
  MvPolynomial.aeval Germ.coordinate

@[simp]
theorem coordinatePolynomialAlgHom_X {n : ℕ} (i : Fin n) :
    Germ.coordinatePolynomialAlgHom n (MvPolynomial.X i) =
      Germ.coordinate i := by
  simp [Germ.coordinatePolynomialAlgHom]

@[simp]
theorem coordinatePolynomialAlgHom_C {n : ℕ} (c : ℂ) :
    Germ.coordinatePolynomialAlgHom n (MvPolynomial.C c) =
      Germ.constRingHom n c := by
  rw [Germ.coordinatePolynomialAlgHom, MvPolynomial.aeval_C,
    RingHom.algebraMap_toAlgebra]

/-- Coordinate evaluation agrees with the germ of the polynomial function. -/
theorem coordinatePolynomialAlgHom_eq_ofFunction {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) :
    Germ.coordinatePolynomialAlgHom n p =
      Germ.ofFunction (fun z : Source n ↦ MvPolynomial.eval z p)
        ((AnalyticOnNhd.eval_mvPolynomial p) 0 (Set.mem_univ 0)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [Germ.coordinatePolynomialAlgHom_C]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by simp
  | add p q hp hq =>
      rw [map_add, hp, hq]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by simp
  | mul_X p i hp =>
      rw [map_mul, hp, Germ.coordinatePolynomialAlgHom_X]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by simp

/-- Every nonempty open disc in `ℂ` is infinite. -/
theorem complex_ball_infinite {r : ℝ} (hr : 0 < r) :
    (Metric.ball (0 : ℂ) r).Infinite := by
  let interval : Set ℝ := Set.Ioo 0 r
  have hinterval : interval.Infinite := Set.Ioo_infinite hr
  have himage : ((fun x : ℝ ↦ (x : ℂ)) '' interval).Infinite :=
    hinterval.image Complex.ofReal_injective.injOn
  apply himage.mono
  rintro z ⟨x, hx, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real]
  exact abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩

/-- A polynomial that vanishes as an analytic germ is the zero polynomial. -/
theorem coordinatePolynomialAlgHom_eq_zero_iff {n : ℕ}
    {p : MvPolynomial (Fin n) ℂ} :
    Germ.coordinatePolynomialAlgHom n p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    rw [Germ.coordinatePolynomialAlgHom_eq_ofFunction] at hp
    have hvalue :
        ((Germ.ofFunction (fun z : Source n ↦ MvPolynomial.eval z p)
          ((AnalyticOnNhd.eval_mvPolynomial p) 0 (Set.mem_univ 0)) : Germ n) :
            FunctionGerm n) = 0 := congrArg Subtype.val hp
    have heventually :
        (fun z : Source n ↦ MvPolynomial.eval z p) =ᶠ[𝓝 0]
          (fun _ ↦ 0) := Filter.Germ.coe_eq.mp hvalue
    rcases Metric.eventually_nhds_iff.mp heventually with
      ⟨r, hr, hball⟩
    apply MvPolynomial.funext_set
      (fun _ : Fin n ↦ Metric.ball (0 : ℂ) r)
      (fun _ ↦ Germ.complex_ball_infinite hr)
    intro z hz
    have hzNorm : ‖z‖ < r := by
      apply (@pi_norm_lt_iff (Fin n) (fun _ : Fin n ↦ ℂ)
        inferInstance (fun _ ↦ inferInstance) z r hr).mpr
      intro i
      simpa only [Metric.mem_ball, dist_zero_right] using
        hz i (Set.mem_univ i)
    have hzBall : z ∈ Metric.ball (0 : Source n) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hzNorm
    simpa using hball hzBall
  · rintro rfl
    exact map_zero _

/-- The coordinate polynomial evaluation map is injective. -/
theorem coordinatePolynomialAlgHom_injective (n : ℕ) :
    Function.Injective (Germ.coordinatePolynomialAlgHom n) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro p hp
  exact Germ.coordinatePolynomialAlgHom_eq_zero_iff.mp hp

/-- The ideal of polynomial variables maps onto the maximal ideal of the
analytic germ ring. -/
theorem map_idealOfVars_coordinatePolynomialAlgHom (n : ℕ) :
    Ideal.map (Germ.coordinatePolynomialAlgHom n)
        (MvPolynomial.idealOfVars (Fin n) ℂ) =
      Germ.maximalIdeal n := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  convert Germ.span_range_coordinate_eq_maximalIdeal n using 2
  ext q
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (Germ.coordinatePolynomialAlgHom_X i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩,
      Germ.coordinatePolynomialAlgHom_X i⟩

/-- Every coordinate monomial used in a finite jet belongs to the polynomial
coordinate subalgebra. -/
theorem jetMonomial_mem_coordinatePolynomialRange {n N : ℕ}
    {q : Germ n} (hq : q ∈ Germ.jetMonomials n N) :
    q ∈ (Germ.coordinatePolynomialAlgHom n).range := by
  induction N generalizing q with
  | zero =>
      simp [Germ.jetMonomials] at hq
  | succ N ih =>
      simp only [Germ.jetMonomials, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_univ,
        true_and, Finset.mem_image] at hq
      rcases hq with rfl | ⟨i, r, hr, rfl⟩
      · exact ⟨1, map_one _⟩
      · rcases ih hr with ⟨p, hp⟩
        refine ⟨MvPolynomial.X i * p, ?_⟩
        rw [map_mul, hp]
        have hi : (Germ.coordinatePolynomialAlgHom n).toRingHom
            (MvPolynomial.X i) = Germ.coordinate i :=
          Germ.coordinatePolynomialAlgHom_X i
        rw [hi]

/-- The span of the coordinate monomials used in a finite jet is contained
in the polynomial coordinate subalgebra. -/
theorem span_jetMonomials_le_coordinatePolynomialRange (n N : ℕ) :
    Submodule.span ℂ (Germ.jetMonomials n N : Set (Germ n)) ≤
      (Germ.coordinatePolynomialAlgHom n).range.toSubmodule := by
  rw [Submodule.span_le]
  intro q hq
  exact Germ.jetMonomial_mem_coordinatePolynomialRange hq

/-- Every analytic germ is congruent to a polynomial coordinate germ modulo
an arbitrary power of the maximal ideal. -/
theorem exists_coordinatePolynomial_mod_maximalIdeal_pow
    (n N : ℕ) (g : Germ n) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      g - Germ.coordinatePolynomialAlgHom n p ∈
        Germ.maximalIdeal n ^ N := by
  rcases Germ.exists_jetApproximation n N g with ⟨q, hq, hrem⟩
  have hqRange :
      q ∈ (Germ.coordinatePolynomialAlgHom n).range.toSubmodule :=
    Germ.span_jetMonomials_le_coordinatePolynomialRange n N hq
  rcases hqRange with ⟨p, hp⟩
  exact ⟨p, hp ▸ hrem⟩

end Germ

end OnLeConjecture.Analytic
