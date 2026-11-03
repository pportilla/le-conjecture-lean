/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothDivision
public import OnLeConjecture.Analytic.TaylorSeries
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Analytic coordinate expansion and formal preparation

This file constructs the expansion of an analytic germ in powers of its first
coordinate. Each coefficient is an analytic germ in the remaining variables.
It also records the finite Taylor formula obtained by iterating analytic
Hadamard division.

The file proves formal Weierstrass preparation in the completed Taylor ring.
It characterizes convergent one variable formal series by positivity of their
analytic radius and states the remaining two variable image closure condition
as a proposition equivalent to analytic Weierstrass preparation.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Division by the first coordinate with a remainder independent of that
coordinate. -/
theorem exists_unique_firstCoordinate_division {n : ℕ}
    (f : Germ (n + 1)) :
    ∃! qr : Germ (n + 1) × Germ n,
      f = Germ.coordinate (0 : Fin (n + 1)) * qr.1 +
        Germ.hyperplaneExtension n qr.2 := by
  let r : Germ n := Germ.hyperplaneRestriction n f
  have hdifference :
      f - Germ.hyperplaneExtension n r ∈
        RingHom.ker (Germ.hyperplaneRestriction n) := by
    rw [RingHom.mem_ker, map_sub]
    change Germ.hyperplaneRestriction n f -
      Germ.hyperplaneRestriction n (Germ.hyperplaneExtension n r) = 0
    have hext : Germ.hyperplaneRestriction n
        (Germ.hyperplaneExtension n r) = r := by
      simpa using DFunLike.congr_fun
        (Germ.hyperplaneRestriction_comp_extension n) r
    rw [hext]
    simp [r]
  rw [Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero,
    Ideal.mem_span_singleton] at hdifference
  rcases hdifference with ⟨q, hq⟩
  refine ⟨⟨q, r⟩, ?_, ?_⟩
  · exact sub_eq_iff_eq_add.mp hq
  · intro qr hqr
    rcases qr with ⟨q', r'⟩
    have hremainder := congrArg (Germ.hyperplaneRestriction n) hqr
    simp only [map_add, map_mul,
      Germ.hyperplaneRestriction_coordinate_zero, zero_mul, zero_add]
      at hremainder
    have hext : Germ.hyperplaneRestriction n
        (Germ.hyperplaneExtension n r') = r' := by
      simpa using DFunLike.congr_fun
        (Germ.hyperplaneRestriction_comp_extension n) r'
    rw [hext] at hremainder
    have hr : r' = r := by
      change r = r' at hremainder
      exact hremainder.symm
    rw [hr] at hqr
    have hcoordinate : Germ.coordinate (0 : Fin (n + 1)) * q' =
        Germ.coordinate (0 : Fin (n + 1)) * q := by
      calc
        Germ.coordinate (0 : Fin (n + 1)) * q' =
            f - Germ.hyperplaneExtension n r :=
          eq_sub_iff_add_eq.mpr hqr.symm
        _ = Germ.coordinate (0 : Fin (n + 1)) * q := hq
    have hcoordinateNe :
        Germ.coordinate (0 : Fin (n + 1)) ≠ 0 := by
      intro hzero
      have hd := congrArg Germ.differential hzero
      have happ := congrArg
        (fun L : Source (n + 1) →L[ℂ] ℂ ↦
          L (firstCoordinateVector n)) hd
      simp [firstCoordinateVector] at happ
    have hq' : q' = q := mul_left_cancel₀ hcoordinateNe hcoordinate
    exact Prod.ext hq' hr

/-- The quotient in analytic division by the first coordinate. -/
@[expose] noncomputable def firstCoordinateTail {n : ℕ}
    (f : Germ (n + 1)) : Germ (n + 1) :=
  (Germ.exists_unique_firstCoordinate_division f).choose.1

/-- The constant coefficient in the expansion in the first coordinate. -/
@[expose] noncomputable def firstCoordinateCoefficient {n : ℕ}
    (f : Germ (n + 1)) : Germ n :=
  Germ.hyperplaneRestriction n f

/-- The canonical first coordinate division formula. -/
theorem firstCoordinate_decomposition {n : ℕ}
    (f : Germ (n + 1)) :
    f = Germ.coordinate (0 : Fin (n + 1)) *
        Germ.firstCoordinateTail f +
      Germ.hyperplaneExtension n (Germ.firstCoordinateCoefficient f) := by
  let qr := (Germ.exists_unique_firstCoordinate_division f).choose
  have hqr : f = Germ.coordinate (0 : Fin (n + 1)) * qr.1 +
      Germ.hyperplaneExtension n qr.2 :=
    (Germ.exists_unique_firstCoordinate_division f).choose_spec.1
  have hremainder := congrArg (Germ.hyperplaneRestriction n) hqr
  simp only [map_add, map_mul,
    Germ.hyperplaneRestriction_coordinate_zero, zero_mul, zero_add]
    at hremainder
  have hext : Germ.hyperplaneRestriction n
      (Germ.hyperplaneExtension n qr.2) = qr.2 := by
    simpa using DFunLike.congr_fun
      (Germ.hyperplaneRestriction_comp_extension n) qr.2
  rw [hext] at hremainder
  have hsecond : qr.2 = Germ.firstCoordinateCoefficient f := by
    exact hremainder.symm
  change f = Germ.coordinate (0 : Fin (n + 1)) * qr.1 +
    Germ.hyperplaneExtension n (Germ.firstCoordinateCoefficient f)
  rw [← hsecond]
  exact hqr

/-- The quotient and remainder in first coordinate division are determined
by the division formula. -/
theorem firstCoordinate_division_eq {n : ℕ}
    {f q : Germ (n + 1)} {r : Germ n}
    (h : f = Germ.coordinate (0 : Fin (n + 1)) * q +
      Germ.hyperplaneExtension n r) :
    Germ.firstCoordinateTail f = q ∧
      Germ.firstCoordinateCoefficient f = r := by
  let qr := (Germ.exists_unique_firstCoordinate_division f).choose
  have hpair : (q, r) = qr :=
    (Germ.exists_unique_firstCoordinate_division f).choose_spec.2 (q, r) h
  constructor
  · change qr.1 = q
    exact (congrArg Prod.fst hpair).symm
  · have hremainder := congrArg (Germ.hyperplaneRestriction n) h
    simp only [map_add, map_mul,
      Germ.hyperplaneRestriction_coordinate_zero, zero_mul, zero_add]
      at hremainder
    have hext : Germ.hyperplaneRestriction n
        (Germ.hyperplaneExtension n r) = r := by
      simpa using DFunLike.congr_fun
        (Germ.hyperplaneRestriction_comp_extension n) r
    rw [hext] at hremainder
    exact hremainder

@[simp]
theorem firstCoordinateCoefficient_add {n : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateCoefficient (f + g) =
      Germ.firstCoordinateCoefficient f +
        Germ.firstCoordinateCoefficient g := by
  exact map_add (Germ.hyperplaneRestriction n) f g

@[simp]
theorem firstCoordinateCoefficient_mul {n : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateCoefficient (f * g) =
      Germ.firstCoordinateCoefficient f *
        Germ.firstCoordinateCoefficient g := by
  exact map_mul (Germ.hyperplaneRestriction n) f g

@[simp]
theorem firstCoordinateCoefficient_zero {n : ℕ} :
    Germ.firstCoordinateCoefficient (0 : Germ (n + 1)) = 0 := by
  exact map_zero (Germ.hyperplaneRestriction n)

@[simp]
theorem firstCoordinateCoefficient_one {n : ℕ} :
    Germ.firstCoordinateCoefficient (1 : Germ (n + 1)) = 1 := by
  exact map_one (Germ.hyperplaneRestriction n)

@[simp]
theorem firstCoordinateTail_zero {n : ℕ} :
    Germ.firstCoordinateTail (0 : Germ (n + 1)) = 0 := by
  exact (Germ.firstCoordinate_division_eq (n := n)
    (f := 0) (q := 0) (r := 0) (by simp)).1

@[simp]
theorem firstCoordinateTail_one {n : ℕ} :
    Germ.firstCoordinateTail (1 : Germ (n + 1)) = 0 := by
  exact (Germ.firstCoordinate_division_eq (n := n)
    (f := 1) (q := 0) (r := 1) (by simp)).1

@[simp]
theorem firstCoordinateTail_add {n : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTail (f + g) =
      Germ.firstCoordinateTail f + Germ.firstCoordinateTail g := by
  have hdivision : f + g =
      Germ.coordinate (0 : Fin (n + 1)) *
          (Germ.firstCoordinateTail f + Germ.firstCoordinateTail g) +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f +
            Germ.firstCoordinateCoefficient g) := by
    calc
      f + g =
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail f +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient f)) +
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail g +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient g)) :=
        congrArg₂ (fun a b ↦ a + b) (Germ.firstCoordinate_decomposition f)
          (Germ.firstCoordinate_decomposition g)
      _ = _ := by
        rw [map_add]
        ring
  exact (Germ.firstCoordinate_division_eq hdivision).1

@[simp]
theorem firstCoordinateTail_mul {n : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTail (f * g) =
      Germ.coordinate (0 : Fin (n + 1)) *
          Germ.firstCoordinateTail f * Germ.firstCoordinateTail g +
        Germ.firstCoordinateTail f *
          Germ.hyperplaneExtension n
            (Germ.firstCoordinateCoefficient g) +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f) *
            Germ.firstCoordinateTail g := by
  have hdivision : f * g =
      Germ.coordinate (0 : Fin (n + 1)) *
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail f * Germ.firstCoordinateTail g +
            Germ.firstCoordinateTail f *
              Germ.hyperplaneExtension n
                (Germ.firstCoordinateCoefficient g) +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient f) *
                Germ.firstCoordinateTail g) +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f *
            Germ.firstCoordinateCoefficient g) := by
    calc
      f * g =
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail f +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient f)) *
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail g +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient g)) :=
        congrArg₂ (fun a b ↦ a * b) (Germ.firstCoordinate_decomposition f)
          (Germ.firstCoordinate_decomposition g)
      _ = _ := by
        rw [map_mul]
        ring
  exact (Germ.firstCoordinate_division_eq hdivision).1

/-- A form of the product rule for the quotient which keeps one factor
undivided. -/
theorem firstCoordinateTail_mul' {n : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTail (f * g) =
      Germ.firstCoordinateTail f * g +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f) *
            Germ.firstCoordinateTail g := by
  have hproduct := congrArg
    (fun h ↦ Germ.firstCoordinateTail f * h)
    (Germ.firstCoordinate_decomposition g)
  calc
    Germ.firstCoordinateTail (f * g) =
        Germ.coordinate (0 : Fin (n + 1)) *
            Germ.firstCoordinateTail f * Germ.firstCoordinateTail g +
          Germ.firstCoordinateTail f *
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient g) +
          Germ.hyperplaneExtension n
            (Germ.firstCoordinateCoefficient f) *
              Germ.firstCoordinateTail g :=
      Germ.firstCoordinateTail_mul f g
    _ = Germ.firstCoordinateTail f *
          (Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail g +
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateCoefficient g)) +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f) *
            Germ.firstCoordinateTail g := by ring
    _ = Germ.firstCoordinateTail f * g +
        Germ.hyperplaneExtension n
          (Germ.firstCoordinateCoefficient f) *
            Germ.firstCoordinateTail g := by rw [← hproduct]

@[simp]
theorem firstCoordinateTail_coordinate_mul {n : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTail
        (Germ.coordinate (0 : Fin (n + 1)) * f) = f := by
  exact (Germ.firstCoordinate_division_eq (n := n)
    (f := Germ.coordinate (0 : Fin (n + 1)) * f)
    (q := f) (r := 0) (by simp)).1

@[simp]
theorem firstCoordinateTail_hyperplaneExtension {n : ℕ}
    (r : Germ n) :
    Germ.firstCoordinateTail (Germ.hyperplaneExtension n r) = 0 := by
  exact (Germ.firstCoordinate_division_eq (n := n)
    (f := Germ.hyperplaneExtension n r)
    (q := 0) (r := r) (by simp)).1

@[simp]
theorem firstCoordinateCoefficient_hyperplaneExtension {n : ℕ}
    (r : Germ n) :
    Germ.firstCoordinateCoefficient (Germ.hyperplaneExtension n r) = r := by
  exact DFunLike.congr_fun
    (Germ.hyperplaneRestriction_comp_extension n) r

/-- Iterated quotient by the first coordinate. -/
@[expose] noncomputable def firstCoordinateTailIterate {n : ℕ}
    (k : ℕ) (f : Germ (n + 1)) : Germ (n + 1) :=
  (Germ.firstCoordinateTail^[k]) f

/-- The `k`th analytic coefficient in the expansion in the first
coordinate. -/
@[expose] noncomputable def firstCoordinateTaylorCoefficient {n : ℕ}
    (k : ℕ) (f : Germ (n + 1)) : Germ n :=
  Germ.firstCoordinateCoefficient (Germ.firstCoordinateTailIterate k f)

@[simp]
theorem firstCoordinateTailIterate_zero {n : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTailIterate 0 f = f := by
  simp [Germ.firstCoordinateTailIterate]

@[simp]
theorem firstCoordinateTailIterate_succ {n k : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTailIterate (k + 1) f =
      Germ.firstCoordinateTail
        (Germ.firstCoordinateTailIterate k f) := by
  simp [Germ.firstCoordinateTailIterate, Function.iterate_succ_apply']

/-- Iterating the quotient after one division agrees with one further
iteration. -/
theorem firstCoordinateTailIterate_tail {n k : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTailIterate k (Germ.firstCoordinateTail f) =
      Germ.firstCoordinateTailIterate (k + 1) f := by
  simp [Germ.firstCoordinateTailIterate,
    Function.iterate_succ_apply]

@[simp]
theorem firstCoordinateTailIterate_zero_germ {n k : ℕ} :
    Germ.firstCoordinateTailIterate k (0 : Germ (n + 1)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTailIterate_succ, ih,
        Germ.firstCoordinateTail_zero]

/-- Iterated first coordinate division preserves addition. -/
theorem firstCoordinateTailIterate_add {n k : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTailIterate k (f + g) =
      Germ.firstCoordinateTailIterate k f +
        Germ.firstCoordinateTailIterate k g := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl]
      calc
        Germ.firstCoordinateTailIterate (k + 1) (f + g) =
            Germ.firstCoordinateTail
              (Germ.firstCoordinateTailIterate k (f + g)) :=
          Germ.firstCoordinateTailIterate_succ (f + g)
        _ = Germ.firstCoordinateTail
            (Germ.firstCoordinateTailIterate k f +
              Germ.firstCoordinateTailIterate k g) := by rw [ih]
        _ = Germ.firstCoordinateTail
              (Germ.firstCoordinateTailIterate k f) +
            Germ.firstCoordinateTail
              (Germ.firstCoordinateTailIterate k g) :=
          Germ.firstCoordinateTail_add _ _
        _ = Germ.firstCoordinateTailIterate (k + 1) f +
            Germ.firstCoordinateTailIterate (k + 1) g := by
          rw [Germ.firstCoordinateTailIterate_succ,
            Germ.firstCoordinateTailIterate_succ]

@[simp]
theorem firstCoordinateTaylorCoefficient_zero {n : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTaylorCoefficient 0 f =
      Germ.hyperplaneRestriction n f := by
  rfl

@[simp]
theorem firstCoordinateTaylorCoefficient_zero_germ {n k : ℕ} :
    Germ.firstCoordinateTaylorCoefficient k (0 : Germ (n + 1)) = 0 := by
  simp [Germ.firstCoordinateTaylorCoefficient]

/-- The analytic Taylor coefficients preserve addition. -/
theorem firstCoordinateTaylorCoefficient_add {n k : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTaylorCoefficient k (f + g) =
      Germ.firstCoordinateTaylorCoefficient k f +
        Germ.firstCoordinateTaylorCoefficient k g := by
  simp [Germ.firstCoordinateTaylorCoefficient,
    Germ.firstCoordinateTailIterate_add]

/-- Passing to the next coefficient is the same as first dividing once. -/
theorem firstCoordinateTaylorCoefficient_succ {n k : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateTaylorCoefficient (k + 1) f =
      Germ.firstCoordinateTaylorCoefficient k
        (Germ.firstCoordinateTail f) := by
  simp only [Germ.firstCoordinateTaylorCoefficient]
  congr 1

/-- Multiplication by a germ independent of the first coordinate commutes
with taking the first coordinate quotient. -/
theorem firstCoordinateTail_hyperplaneExtension_mul {n : ℕ}
    (r : Germ n) (f : Germ (n + 1)) :
    Germ.firstCoordinateTail (Germ.hyperplaneExtension n r * f) =
      Germ.hyperplaneExtension n r * Germ.firstCoordinateTail f := by
  rw [Germ.firstCoordinateTail_mul']
  simp

/-- Multiplication by a coefficient germ acts coefficientwise on the first
coordinate expansion. -/
theorem firstCoordinateTaylorCoefficient_hyperplaneExtension_mul
    {n k : ℕ} (r : Germ n) (f : Germ (n + 1)) :
    Germ.firstCoordinateTaylorCoefficient k
        (Germ.hyperplaneExtension n r * f) =
      r * Germ.firstCoordinateTaylorCoefficient k f := by
  induction k generalizing f with
  | zero =>
      rw [Germ.firstCoordinateTaylorCoefficient_zero,
        Germ.firstCoordinateTaylorCoefficient_zero, map_mul]
      have hext : Germ.hyperplaneRestriction n
          (Germ.hyperplaneExtension n r) = r := by
        simpa using DFunLike.congr_fun
          (Germ.hyperplaneRestriction_comp_extension n) r
      rw [hext]
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTaylorCoefficient_succ,
        Germ.firstCoordinateTail_hyperplaneExtension_mul, ih,
        ← Germ.firstCoordinateTaylorCoefficient_succ]

/-- The coefficients of a product satisfy the Cauchy product formula. -/
theorem firstCoordinateTaylorCoefficient_mul {n k : ℕ}
    (f g : Germ (n + 1)) :
    Germ.firstCoordinateTaylorCoefficient k (f * g) =
      ∑ p ∈ Finset.antidiagonal k,
        Germ.firstCoordinateTaylorCoefficient p.1 f *
          Germ.firstCoordinateTaylorCoefficient p.2 g := by
  induction k generalizing f g with
  | zero =>
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        Germ.firstCoordinateTaylorCoefficient_zero]
      exact map_mul (Germ.hyperplaneRestriction n) f g
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTaylorCoefficient_succ,
        Germ.firstCoordinateTail_mul',
        Germ.firstCoordinateTaylorCoefficient_add, ih,
        Germ.firstCoordinateTaylorCoefficient_hyperplaneExtension_mul,
        Finset.Nat.sum_antidiagonal_succ]
      rw [← Germ.firstCoordinateTaylorCoefficient_succ g]
      calc
        (∑ p ∈ Finset.antidiagonal k,
              Germ.firstCoordinateTaylorCoefficient p.1
                  (Germ.firstCoordinateTail f) *
                Germ.firstCoordinateTaylorCoefficient p.2 g) +
            Germ.firstCoordinateCoefficient f *
              Germ.firstCoordinateTaylorCoefficient (k + 1) g =
          Germ.firstCoordinateCoefficient f *
              Germ.firstCoordinateTaylorCoefficient (k + 1) g +
            ∑ p ∈ Finset.antidiagonal k,
              Germ.firstCoordinateTaylorCoefficient p.1
                  (Germ.firstCoordinateTail f) *
                Germ.firstCoordinateTaylorCoefficient p.2 g := by
          rw [add_comm]
        _ = Germ.firstCoordinateTaylorCoefficient 0 f *
              Germ.firstCoordinateTaylorCoefficient (k + 1) g +
            ∑ p ∈ Finset.antidiagonal k,
              Germ.firstCoordinateTaylorCoefficient (p.1 + 1) f *
                Germ.firstCoordinateTaylorCoefficient p.2 g := by
          rw [Germ.firstCoordinateTaylorCoefficient_zero]
          congr 1

@[simp]
theorem firstCoordinateTaylorCoefficient_one {n k : ℕ} :
    Germ.firstCoordinateTaylorCoefficient k (1 : Germ (n + 1)) =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTaylorCoefficient_succ,
        Germ.firstCoordinateTail_one,
        Germ.firstCoordinateTaylorCoefficient_zero_germ]
      simp

/-- The formal series in the first coordinate whose coefficients are
analytic germs in the remaining variables. -/
@[expose] noncomputable def firstCoordinateFormalSeries {n : ℕ}
    (f : Germ (n + 1)) : PowerSeries (Germ n) :=
  PowerSeries.mk fun k ↦ Germ.firstCoordinateTaylorCoefficient k f

@[simp]
theorem firstCoordinateFormalSeries_coeff {n k : ℕ}
    (f : Germ (n + 1)) :
    PowerSeries.coeff k (Germ.firstCoordinateFormalSeries f) =
      Germ.firstCoordinateTaylorCoefficient k f := by
  simp [Germ.firstCoordinateFormalSeries]

/-- Expansion in the first coordinate is a ring homomorphism to formal power
series over the analytic parameter ring. -/
@[expose] noncomputable def firstCoordinateFormalRingHom (n : ℕ) :
    Germ (n + 1) →+* PowerSeries (Germ n) where
  toFun := Germ.firstCoordinateFormalSeries
  map_zero' := by
    ext k
    simp
  map_one' := by
    ext k
    simp [PowerSeries.coeff_one]
  map_add' f g := by
    ext k
    simp [Germ.firstCoordinateTaylorCoefficient_add]
  map_mul' f g := by
    ext k
    rw [Germ.firstCoordinateFormalSeries_coeff,
      Germ.firstCoordinateTaylorCoefficient_mul,
      PowerSeries.coeff_mul]
    simp only [Germ.firstCoordinateFormalSeries_coeff]

@[simp]
theorem firstCoordinateFormalRingHom_apply {n : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateFormalRingHom n f =
      Germ.firstCoordinateFormalSeries f :=
  rfl

/-- The formal first coordinate expansion determines the analytic germ. -/
theorem firstCoordinateFormalRingHom_injective (n : ℕ) :
    Function.Injective (Germ.firstCoordinateFormalRingHom n) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro f hf
  apply Germ.eq_zero_of_mem_maximalIdeal_pow_all
  intro d
  have hcoefficient (k : ℕ) :
      Germ.firstCoordinateTaylorCoefficient k f = 0 := by
    have hk := congrArg (PowerSeries.coeff k) hf
    simpa using hk
  induction d generalizing f with
  | zero => simp
  | succ d ih =>
      have hconstant : Germ.firstCoordinateCoefficient f = 0 := by
        change Germ.hyperplaneRestriction n f = 0
        simpa using hcoefficient 0
      have hfactor : f = Germ.coordinate (0 : Fin (n + 1)) *
          Germ.firstCoordinateTail f := by
        calc
          f = Germ.coordinate (0 : Fin (n + 1)) *
                Germ.firstCoordinateTail f +
              Germ.hyperplaneExtension n
                (Germ.firstCoordinateCoefficient f) :=
            Germ.firstCoordinate_decomposition f
          _ = Germ.coordinate (0 : Fin (n + 1)) *
              Germ.firstCoordinateTail f := by
            rw [hconstant]
            simp
      rw [hfactor, pow_succ']
      apply Ideal.mul_mem_mul
      · exact Germ.coordinate_mem_maximalIdeal (0 : Fin (n + 1))
      · apply ih
        · apply PowerSeries.ext
          intro k
          rw [Germ.firstCoordinateFormalRingHom_apply,
            Germ.firstCoordinateFormalSeries_coeff]
          simp only [map_zero]
          rw [← Germ.firstCoordinateTaylorCoefficient_succ]
          exact hcoefficient (k + 1)
        · intro k
          rw [← Germ.firstCoordinateTaylorCoefficient_succ]
          exact hcoefficient (k + 1)

/-- The formal first coordinate expansion of a germ independent of that
coordinate is constant. -/
theorem firstCoordinateFormalRingHom_hyperplaneExtension {n : ℕ}
    (r : Germ n) :
    Germ.firstCoordinateFormalRingHom n
        (Germ.hyperplaneExtension n r) = PowerSeries.C r := by
  apply PowerSeries.ext
  intro k
  rw [Germ.firstCoordinateFormalRingHom_apply,
    Germ.firstCoordinateFormalSeries_coeff]
  cases k with
  | zero =>
      rw [PowerSeries.coeff_C, if_pos rfl]
      change Germ.firstCoordinateCoefficient
        (Germ.hyperplaneExtension n r) = r
      exact Germ.firstCoordinateCoefficient_hyperplaneExtension r
  | succ k =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTaylorCoefficient_succ,
        Germ.firstCoordinateTail_hyperplaneExtension,
        Germ.firstCoordinateTaylorCoefficient_zero_germ]
      simp

/-- Dividing the first coordinate once leaves the constant germ one. -/
@[simp]
theorem firstCoordinateTail_coordinate {n : ℕ} :
    Germ.firstCoordinateTail
      (Germ.coordinate (0 : Fin (n + 1))) = 1 := by
  simpa using Germ.firstCoordinateTail_coordinate_mul
    (n := n) (1 : Germ (n + 1))

/-- The formal first coordinate expansion sends the first coordinate to the
formal variable. -/
theorem firstCoordinateFormalRingHom_coordinate {n : ℕ} :
    Germ.firstCoordinateFormalRingHom n
        (Germ.coordinate (0 : Fin (n + 1))) = PowerSeries.X := by
  apply PowerSeries.ext
  intro k
  rw [Germ.firstCoordinateFormalRingHom_apply,
    Germ.firstCoordinateFormalSeries_coeff]
  cases k with
  | zero => simp
  | succ k =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTaylorCoefficient_succ,
        Germ.firstCoordinateTail_coordinate]
      cases k with
      | zero => simp
      | succ k =>
          rw [show k + 1 = k + 1 from rfl,
            Germ.firstCoordinateTaylorCoefficient_succ,
            Germ.firstCoordinateTail_one,
            Germ.firstCoordinateTaylorCoefficient_zero_germ]
          rw [PowerSeries.coeff_X, if_neg (by omega)]

/-- Evaluation is the constant coefficient of the Taylor series of a one
variable analytic germ. -/
theorem constantCoeff_oneVariableTaylorSeries (q : Germ 1) :
    PowerSeries.constantCoeff (Germ.oneVariableTaylorSeries q) =
      Germ.valueRingHom 1 q := by
  rcases q with ⟨q, hq⟩
  induction q using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hq
      change PowerSeries.constantCoeff
          (Germ.functionTaylorSeries
            (Germ.oneVariableRepresentative f)) = f 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [Germ.functionTaylorSeries_coeff, Nat.factorial_zero,
        Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
      change f (Germ.oneVariableEquiv.symm 0) = f 0
      congr 1

/-- The completed Taylor expansion of a plane analytic germ. The outer
variable is the first source coordinate and the inner variable is the
parameter coordinate. -/
@[expose] noncomputable def completedPlaneTaylorRingHom :
    Germ 2 →+* PowerSeries (PowerSeries ℂ) :=
  (PowerSeries.map Germ.oneVariableTaylorRingHom).comp
    (Germ.firstCoordinateFormalRingHom 1)

@[simp]
theorem completedPlaneTaylorRingHom_coeff (k : ℕ) (f : Germ 2) :
    PowerSeries.coeff k (Germ.completedPlaneTaylorRingHom f) =
      Germ.oneVariableTaylorSeries
        (Germ.firstCoordinateTaylorCoefficient k f) := by
  simp [Germ.completedPlaneTaylorRingHom,
    Germ.firstCoordinateFormalSeries]

/-- Completion is injective on plane analytic germs. -/
theorem completedPlaneTaylorRingHom_injective :
    Function.Injective Germ.completedPlaneTaylorRingHom :=
  (PowerSeries.map_injective Germ.oneVariableTaylorRingHom
    Germ.oneVariableTaylorRingHom_injective).comp
      (Germ.firstCoordinateFormalRingHom_injective 1)

/-- The completed plane Taylor expansion of a germ depending only on the
parameter is constant in the first coordinate. -/
theorem completedPlaneTaylorRingHom_hyperplaneExtension (r : Germ 1) :
    Germ.completedPlaneTaylorRingHom (Germ.hyperplaneExtension 1 r) =
      PowerSeries.C (Germ.oneVariableTaylorRingHom r) := by
  rw [Germ.completedPlaneTaylorRingHom]
  change PowerSeries.map Germ.oneVariableTaylorRingHom
    (Germ.firstCoordinateFormalRingHom 1
      (Germ.hyperplaneExtension 1 r)) = _
  rw [Germ.firstCoordinateFormalRingHom_hyperplaneExtension]
  exact PowerSeries.map_C _ _

/-- The completed plane Taylor expansion sends the first coordinate to the
outer formal variable. -/
theorem completedPlaneTaylorRingHom_coordinate :
    Germ.completedPlaneTaylorRingHom
      (Germ.coordinate (0 : Fin 2)) = PowerSeries.X := by
  rw [Germ.completedPlaneTaylorRingHom]
  change PowerSeries.map Germ.oneVariableTaylorRingHom
    (Germ.firstCoordinateFormalRingHom 1
      (Germ.coordinate (0 : Fin 2))) = _
  rw [Germ.firstCoordinateFormalRingHom_coordinate]
  exact PowerSeries.map_X _

/-- The scalar formal multilinear series associated with a formal power
series. -/
@[expose] noncomputable def powerSeriesFormalMultilinearSeries
    (q : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun k ↦ PowerSeries.coeff k q

/-- A formal power series has positive Taylor radius when its associated
scalar formal multilinear series has positive radius. -/
def HasPositiveTaylorRadius (q : PowerSeries ℂ) : Prop :=
  0 < (Germ.powerSeriesFormalMultilinearSeries q).radius

/-- Summing a formal power series of positive Taylor radius recovers the same
formal Taylor coefficients. -/
theorem functionTaylorSeries_sum_of_positiveTaylorRadius
    (q : PowerSeries ℂ) (h : Germ.HasPositiveTaylorRadius q) :
    Germ.functionTaylorSeries
      (Germ.powerSeriesFormalMultilinearSeries q).sum = q := by
  let p := Germ.powerSeriesFormalMultilinearSeries q
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall h
  have hpTaylor := hp.hasFPowerSeriesAt.analyticAt.hasFPowerSeriesAt
  have hseries := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hpTaylor
  apply PowerSeries.ext
  intro k
  have hcoeff := congrArg (fun s ↦ s.coeff k) hseries
  simpa [p, Germ.powerSeriesFormalMultilinearSeries,
    Germ.functionTaylorSeries_coeff, div_eq_mul_inv, mul_comm] using
      hcoeff.symm

/-- A formal power series of positive Taylor radius is the Taylor series of
an analytic germ. -/
theorem exists_oneVariableGerm_of_positiveTaylorRadius
    (q : PowerSeries ℂ) (h : Germ.HasPositiveTaylorRadius q) :
    ∃ g : Germ 1, Germ.oneVariableTaylorRingHom g = q := by
  let p := Germ.powerSeriesFormalMultilinearSeries q
  let f : Source 1 → ℂ := fun z ↦ p.sum (Germ.oneVariableEquiv z)
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall h
  have hpAnalytic : AnalyticAt ℂ p.sum 0 :=
    hp.hasFPowerSeriesAt.analyticAt
  have hf : AnalyticAt ℂ f 0 := by
    have hequiv := Germ.oneVariableEquiv.analyticAt (0 : Source 1)
    have hpAtImage : AnalyticAt ℂ p.sum
        (Germ.oneVariableEquiv (0 : Source 1)) := by
      simpa using hpAnalytic
    have hcomp := hpAtImage.fun_comp hequiv
    simpa [f] using hcomp
  refine ⟨Germ.ofFunction f hf, ?_⟩
  rw [Germ.oneVariableTaylorRingHom_apply,
    Germ.oneVariableTaylorSeries_ofFunction]
  have hrepresentative : Germ.oneVariableRepresentative f = p.sum := by
    funext z
    simp [Germ.oneVariableRepresentative, f]
  rw [hrepresentative]
  exact Germ.functionTaylorSeries_sum_of_positiveTaylorRadius q h

/-- The Taylor series of a one variable analytic germ has positive Taylor
radius. -/
theorem hasPositiveTaylorRadius_oneVariableTaylorRingHom (g : Germ 1) :
    Germ.HasPositiveTaylorRadius (Germ.oneVariableTaylorRingHom g) := by
  rcases g with ⟨g, hg⟩
  change IsAnalyticGerm g at hg
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      have hf : AnalyticAt ℂ f 0 := (isAnalyticGerm_ofFun f).mp hg
      have hfOne := Germ.oneVariableRepresentative_analyticAt hf
      have hp := hfOne.hasFPowerSeriesAt
      rcases hp with ⟨r, hr⟩
      change 0 < (Germ.powerSeriesFormalMultilinearSeries
        (Germ.functionTaylorSeries
          (Germ.oneVariableRepresentative f))).radius
      simpa [Germ.powerSeriesFormalMultilinearSeries,
        Germ.functionTaylorSeries_coeff, div_eq_mul_inv, mul_comm] using
          (lt_of_lt_of_le hr.r_pos hr.r_le)

/-- Positive Taylor radius characterizes the image of the Taylor embedding
of one variable analytic germs. -/
theorem hasPositiveTaylorRadius_iff_mem_range_oneVariableTaylorRingHom
    (q : PowerSeries ℂ) :
    Germ.HasPositiveTaylorRadius q ↔
      q ∈ Set.range Germ.oneVariableTaylorRingHom := by
  constructor
  · exact Germ.exists_oneVariableGerm_of_positiveTaylorRadius q
  · rintro ⟨g, rfl⟩
    exact Germ.hasPositiveTaylorRadius_oneVariableTaylorRingHom g

/-- Finite Taylor expansion in the first coordinate. -/
theorem firstCoordinate_finite_expansion {n d : ℕ}
    (f : Germ (n + 1)) :
    f = ∑ k ∈ Finset.range d,
        Germ.coordinate (0 : Fin (n + 1)) ^ k *
          Germ.hyperplaneExtension n
            (Germ.firstCoordinateTaylorCoefficient k f) +
      Germ.coordinate (0 : Fin (n + 1)) ^ d *
        Germ.firstCoordinateTailIterate d f := by
  induction d with
  | zero => simp
  | succ d ih =>
      have htail := Germ.firstCoordinate_decomposition
        (Germ.firstCoordinateTailIterate d f)
      calc
        f = ∑ k ∈ Finset.range d,
              Germ.coordinate (0 : Fin (n + 1)) ^ k *
                Germ.hyperplaneExtension n
                  (Germ.firstCoordinateTaylorCoefficient k f) +
            Germ.coordinate (0 : Fin (n + 1)) ^ d *
              Germ.firstCoordinateTailIterate d f := ih
        _ = ∑ k ∈ Finset.range d,
              Germ.coordinate (0 : Fin (n + 1)) ^ k *
                Germ.hyperplaneExtension n
                  (Germ.firstCoordinateTaylorCoefficient k f) +
            Germ.coordinate (0 : Fin (n + 1)) ^ d *
              (Germ.coordinate (0 : Fin (n + 1)) *
                  Germ.firstCoordinateTail
                    (Germ.firstCoordinateTailIterate d f) +
                Germ.hyperplaneExtension n
                  (Germ.firstCoordinateCoefficient
                    (Germ.firstCoordinateTailIterate d f))) := by
          exact congrArg
            (fun t ↦
              (∑ k ∈ Finset.range d,
                  Germ.coordinate (0 : Fin (n + 1)) ^ k *
                    Germ.hyperplaneExtension n
                      (Germ.firstCoordinateTaylorCoefficient k f)) +
                Germ.coordinate (0 : Fin (n + 1)) ^ d * t)
            htail
        _ = ∑ k ∈ Finset.range (d + 1),
              Germ.coordinate (0 : Fin (n + 1)) ^ k *
                Germ.hyperplaneExtension n
                  (Germ.firstCoordinateTaylorCoefficient k f) +
            Germ.coordinate (0 : Fin (n + 1)) ^ (d + 1) *
              Germ.firstCoordinateTailIterate (d + 1) f := by
          have hiterate : Germ.firstCoordinateTailIterate (d + 1) f =
              Germ.firstCoordinateTail
                (Germ.firstCoordinateTailIterate d f) :=
            Germ.firstCoordinateTailIterate_succ f
          rw [Finset.sum_range_succ]
          rw [hiterate]
          rw [show Germ.firstCoordinateTaylorCoefficient d f =
              Germ.firstCoordinateCoefficient
                (Germ.firstCoordinateTailIterate d f) from rfl]
          ring

/-- Restriction of the first coordinate to its coordinate axis. -/
@[simp]
theorem lineRestriction_firstCoordinate {n : ℕ} :
    Germ.lineRestriction (firstCoordinateVector n)
        (Germ.coordinate (0 : Fin (n + 1))) =
      Germ.coordinate (0 : Fin 1) := by
  rw [Germ.lineRestriction, PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [Germ.lineGerm]
  change
    ((MapGerm.ofFunction (Germ.lineMap (firstCoordinateVector n))
      ((Germ.lineMap (firstCoordinateVector n)).analyticAt 0)).component 0).1 =
      (Germ.coordinate (0 : Fin 1)).1
  rw [MapGerm.component_ofFunction]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  simp [Germ.lineMap_apply, firstCoordinateVector]

/-- A germ independent of the first coordinate restricts to the constant
given by its value at the origin on the first coordinate axis. -/
@[simp]
theorem lineRestriction_hyperplaneExtension_firstCoordinate {n : ℕ}
    (r : Germ n) :
    Germ.lineRestriction (firstCoordinateVector n)
        (Germ.hyperplaneExtension n r) =
      Germ.constRingHom 1 (Germ.valueRingHom n r) := by
  rcases r with ⟨r, hr⟩
  induction r using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hr
      change Germ.lineRestriction (firstCoordinateVector n)
          (Germ.hyperplaneExtension n (Germ.ofFunction f hr)) =
        Germ.constRingHom 1
          (Germ.valueRingHom n (Germ.ofFunction f hr))
      rw [Germ.hyperplaneExtension_ofFunction,
        Germ.lineRestriction_ofFunction]
      rw [Germ.valueRingHom_ofFunction]
      have hconst : AnalyticAt ℂ (fun _ : Source 1 ↦ f 0) 0 :=
        analyticAt_const
      change Germ.ofFunction _ _ = Germ.ofFunction (fun _ ↦ f 0) hconst
      apply Germ.ofFunction_eq_of_eventuallyEq
      exact Filter.Eventually.of_forall fun z ↦ by
        change f (hyperplaneTail n
          (Germ.lineMap (firstCoordinateVector n) z)) = f 0
        congr 1
        ext i
        simp [Germ.lineMap_apply, hyperplaneTail,
          firstCoordinateVector]

/-- The Taylor series on the first coordinate axis. -/
@[expose] noncomputable def firstCoordinateAxisTaylorSeries {n : ℕ}
    (f : Germ (n + 1)) : PowerSeries ℂ :=
  Germ.oneVariableTaylorSeries
    (Germ.lineRestriction (firstCoordinateVector n) f)

/-- First coordinate division becomes the usual head and tail decomposition
of the Taylor series on the first coordinate axis. -/
theorem firstCoordinateAxisTaylorSeries_decomposition {n : ℕ}
    (f : Germ (n + 1)) :
    Germ.firstCoordinateAxisTaylorSeries f =
      Germ.oneVariableTaylorSeries
          (Germ.coordinate (0 : Fin 1)) *
        Germ.firstCoordinateAxisTaylorSeries
          (Germ.firstCoordinateTail f) +
      PowerSeries.C
        (Germ.valueRingHom n (Germ.firstCoordinateCoefficient f)) := by
  have hmapped := congrArg
    (fun q ↦ Germ.oneVariableTaylorAlgHom
      (Germ.lineRestriction (firstCoordinateVector n) q))
    (Germ.firstCoordinate_decomposition f)
  simp only [map_add, map_mul, Germ.lineRestriction_firstCoordinate,
    Germ.lineRestriction_hyperplaneExtension_firstCoordinate] at hmapped
  have hconstant : Germ.oneVariableTaylorAlgHom
      (Germ.constRingHom 1
        (Germ.valueRingHom n (Germ.firstCoordinateCoefficient f))) =
      PowerSeries.C
        (Germ.valueRingHom n (Germ.firstCoordinateCoefficient f)) := by
    change _ = algebraMap ℂ (PowerSeries ℂ)
        (Germ.valueRingHom n (Germ.firstCoordinateCoefficient f))
    exact Germ.oneVariableTaylorAlgHom.commutes _
  rw [hconstant] at hmapped
  simpa only [Germ.firstCoordinateAxisTaylorSeries,
    Germ.oneVariableTaylorAlgHom_apply] using hmapped

/-- The Taylor series of the coordinate germ is the formal variable. -/
@[simp]
theorem oneVariableTaylorSeries_coordinate :
    Germ.oneVariableTaylorSeries (Germ.coordinate (0 : Fin 1)) =
      (PowerSeries.X : PowerSeries ℂ) := by
  change Germ.functionTaylorSeries
      (Germ.oneVariableRepresentative
        (fun z : Source 1 ↦ z 0)) = PowerSeries.X
  have hrepresentative : Germ.oneVariableRepresentative
      (fun z : Source 1 ↦ z 0) = id := by
    funext z
    simp [Germ.oneVariableRepresentative, Germ.oneVariableEquiv]
  rw [hrepresentative]
  ext k
  by_cases hk0 : k = 0
  · subst k
    simp [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X]
  by_cases hk1 : k = 1
  · subst k
    norm_num [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X]
  · simp [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X, hk0, hk1]

/-- The constant coefficient of the Taylor series on the first coordinate
axis. -/
theorem firstCoordinateAxisTaylorSeries_coeff_zero {n : ℕ}
    (f : Germ (n + 1)) :
    PowerSeries.coeff 0 (Germ.firstCoordinateAxisTaylorSeries f) =
      Germ.valueRingHom n (Germ.firstCoordinateCoefficient f) := by
  rw [Germ.firstCoordinateAxisTaylorSeries_decomposition,
    Germ.oneVariableTaylorSeries_coordinate]
  simp

/-- Removing the constant coefficient shifts the Taylor coefficients on the
first coordinate axis. -/
theorem firstCoordinateAxisTaylorSeries_coeff_succ {n k : ℕ}
    (f : Germ (n + 1)) :
    PowerSeries.coeff (k + 1) (Germ.firstCoordinateAxisTaylorSeries f) =
      PowerSeries.coeff k
        (Germ.firstCoordinateAxisTaylorSeries
          (Germ.firstCoordinateTail f)) := by
  rw [Germ.firstCoordinateAxisTaylorSeries_decomposition,
    Germ.oneVariableTaylorSeries_coordinate, map_add]
  have hpow : (PowerSeries.X : PowerSeries ℂ) = PowerSeries.X ^ 1 := by
    simp
  rw [hpow, show k + 1 = k + 1 from rfl,
    PowerSeries.coeff_X_pow_mul
      (Germ.firstCoordinateAxisTaylorSeries
        (Germ.firstCoordinateTail f)) 1 k]
  simp

/-- The analytic coefficients obtained by Hadamard division are exactly the
Taylor coefficients of the restriction to the first coordinate axis. -/
theorem firstCoordinateAxisTaylorSeries_coeff {n k : ℕ}
    (f : Germ (n + 1)) :
    PowerSeries.coeff k (Germ.firstCoordinateAxisTaylorSeries f) =
      Germ.valueRingHom n
        (Germ.firstCoordinateTaylorCoefficient k f) := by
  induction k generalizing f with
  | zero =>
      exact Germ.firstCoordinateAxisTaylorSeries_coeff_zero f
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateAxisTaylorSeries_coeff_succ]
      rw [ih]
      congr 2

/-- The formal order of the Taylor series of a one variable analytic germ is
its analytic order of vanishing. -/
theorem order_oneVariableTaylorSeries (q : Germ 1) :
    PowerSeries.order (Germ.oneVariableTaylorSeries q) =
      Germ.vanishingOrder q := by
  by_cases hq : q = 0
  · subst q
    have hzero : Germ.oneVariableTaylorSeries (0 : Germ 1) = 0 := by
      change Germ.oneVariableTaylorRingHom 0 = 0
      exact map_zero Germ.oneVariableTaylorRingHom
    rw [hzero]
    simp
  obtain ⟨d, u, hu, hqu⟩ := Germ.exists_eq_coordinate_pow_mul_unit hq
  have hmapUnit : IsUnit (Germ.oneVariableTaylorSeries u) := by
    change IsUnit (Germ.oneVariableTaylorRingHom u)
    exact hu.map Germ.oneVariableTaylorRingHom
  have hunitOrder :
      PowerSeries.order (Germ.oneVariableTaylorSeries u) = 0 := by
    apply (PowerSeries.order_eq_nat (n := 0)).2
    refine ⟨?_, ?_⟩
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (PowerSeries.isUnit_iff_constantCoeff.mp hmapUnit).ne_zero
    · intro i hi
      omega
  have hvanishing : Germ.vanishingOrder q = d :=
    Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hqu
  rw [hvanishing, hqu]
  change PowerSeries.order
      (Germ.oneVariableTaylorRingHom
        (Germ.coordinate (0 : Fin 1) ^ d * u)) = d
  rw [map_mul, map_pow, Germ.oneVariableTaylorRingHom_apply,
    Germ.oneVariableTaylorSeries_coordinate,
    Germ.oneVariableTaylorRingHom_apply, PowerSeries.order_mul,
    PowerSeries.order_X_pow, hunitOrder]
  simp

/-- A germ is regular of order `d` in its first coordinate when its
restriction to the first coordinate axis has order `d`. -/
@[expose] def IsRegularInFirstCoordinateOfOrder {n : ℕ}
    (f : Germ (n + 1)) (d : ℕ) : Prop :=
  Germ.vanishingOrder
    (Germ.lineRestriction (firstCoordinateVector n) f) = d

/-- Regularity of a fixed order is equivalent to vanishing of all preceding
analytic coefficients and nonvanishing of the coefficient of that order at
the origin. -/
theorem isRegularInFirstCoordinateOfOrder_iff {n d : ℕ}
    {f : Germ (n + 1)} :
    Germ.IsRegularInFirstCoordinateOfOrder f d ↔
      Germ.valueRingHom n
          (Germ.firstCoordinateTaylorCoefficient d f) ≠ 0 ∧
        ∀ k, k < d → Germ.valueRingHom n
          (Germ.firstCoordinateTaylorCoefficient k f) = 0 := by
  rw [Germ.IsRegularInFirstCoordinateOfOrder,
    ← Germ.order_oneVariableTaylorSeries]
  change PowerSeries.order (Germ.firstCoordinateAxisTaylorSeries f) = d ↔ _
  rw [PowerSeries.order_eq_nat]
  simp only [Germ.firstCoordinateAxisTaylorSeries_coeff]

/-- Evaluation of an analytic coefficient equals evaluation of the
corresponding iterated quotient. -/
theorem value_firstCoordinateTaylorCoefficient {n k : ℕ}
    (f : Germ (n + 1)) :
    Germ.valueRingHom n
        (Germ.firstCoordinateTaylorCoefficient k f) =
      Germ.valueRingHom (n + 1)
        (Germ.firstCoordinateTailIterate k f) := by
  change Germ.valueRingHom n
      (Germ.hyperplaneRestriction n
        (Germ.firstCoordinateTailIterate k f)) = _
  exact PointedMapGerm.valueRingHom_pullback
    (Germ.hyperplaneInclusionGerm n)
    (Germ.firstCoordinateTailIterate k f)

/-- At the regular order, the iterated analytic quotient is a unit. -/
theorem isUnit_firstCoordinateTailIterate_of_regular {n d : ℕ}
    {f : Germ (n + 1)}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    IsUnit (Germ.firstCoordinateTailIterate d f) := by
  apply Germ.isUnit_of_valueRingHom_ne_zero
  rw [← Germ.value_firstCoordinateTaylorCoefficient]
  exact (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).1

/-- Every coefficient below the regular order vanishes at the origin. -/
theorem firstCoordinateTaylorCoefficient_mem_maximalIdeal_of_lt_order
    {n d k : ℕ} {f : Germ (n + 1)}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d)
    (hk : k < d) :
    Germ.firstCoordinateTaylorCoefficient k f ∈
      Germ.maximalIdeal n := by
  rw [Germ.mem_maximalIdeal_iff]
  exact (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2 k hk

/-- Finite analytic division at the regular order. The leading quotient is a
unit and every lower coefficient vanishes at the origin. -/
theorem exists_finite_expansion_of_regular {n d : ℕ}
    {f : Germ (n + 1)}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    ∃ u : Germ (n + 1), IsUnit u ∧
      f = ∑ k ∈ Finset.range d,
          Germ.coordinate (0 : Fin (n + 1)) ^ k *
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateTaylorCoefficient k f) +
        Germ.coordinate (0 : Fin (n + 1)) ^ d * u ∧
      ∀ k, k < d →
        Germ.firstCoordinateTaylorCoefficient k f ∈
          Germ.maximalIdeal n := by
  refine ⟨Germ.firstCoordinateTailIterate d f,
    Germ.isUnit_firstCoordinateTailIterate_of_regular hregular,
    Germ.firstCoordinate_finite_expansion f, ?_⟩
  intro k hk
  exact Germ.firstCoordinateTaylorCoefficient_mem_maximalIdeal_of_lt_order
    hregular hk

/-- Reduction of the completed plane Taylor series to the residue field has
the same order as restriction of the analytic germ to the first coordinate
axis. -/
theorem order_completedPlaneTaylor_map_residue {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    PowerSeries.order
        ((Germ.completedPlaneTaylorRingHom f).map
          (IsLocalRing.residue (PowerSeries ℂ))) = d := by
  apply (PowerSeries.order_eq_nat (n := d)).2
  constructor
  · rw [PowerSeries.coeff_map,
      Germ.completedPlaneTaylorRingHom_coeff]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).2
    rw [PowerSeries.isUnit_iff_constantCoeff,
      Germ.constantCoeff_oneVariableTaylorSeries]
    apply isUnit_iff_ne_zero.mpr
    exact (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).1
  · intro k hk
    rw [PowerSeries.coeff_map,
      Germ.completedPlaneTaylorRingHom_coeff,
      IsLocalRing.residue_eq_zero_iff,
      ← PowerSeries.ker_coeff_eq_max_ideal,
      RingHom.mem_ker,
      Germ.constantCoeff_oneVariableTaylorSeries]
    exact (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2 k hk

/-- A germ regular in the first coordinate has nonzero image after reducing
its completed Taylor series to the residue field. -/
theorem completedPlaneTaylor_map_residue_ne_zero {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    (Germ.completedPlaneTaylorRingHom f).map
        (IsLocalRing.residue (PowerSeries ℂ)) ≠ 0 := by
  intro hzero
  have horder := Germ.order_completedPlaneTaylor_map_residue hregular
  rw [hzero] at horder
  simp at horder

/-- Formal Weierstrass preparation of the completed Taylor series of a plane
analytic germ. -/
theorem exists_completed_weierstrassFactorization {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    ∃ P : Polynomial (PowerSeries ℂ),
      ∃ U : PowerSeries (PowerSeries ℂ),
        (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization P U := by
  let _ : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  exact PowerSeries.exists_isWeierstrassFactorization
    (Germ.completedPlaneTaylor_map_residue_ne_zero hregular)

/-- The distinguished polynomial in the completed preparation has the
analytic regular order as its degree. -/
theorem natDegree_eq_of_completed_weierstrassFactorization
    {d : ℕ} {f : Germ 2} {P : Polynomial (PowerSeries ℂ)}
    {U : PowerSeries (PowerSeries ℂ)}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d)
    (hfactor : (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization
      P U) :
    P.natDegree = d := by
  have hproper :
      IsLocalRing.maximalIdeal (PowerSeries ℂ) ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal (PowerSeries ℂ)).ne_top
  rw [hfactor.natDegree_eq_toNat_order_map_of_ne_top hproper]
  have horder := Germ.order_completedPlaneTaylor_map_residue hregular
  change PowerSeries.order
      ((Germ.completedPlaneTaylorRingHom f).map
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (PowerSeries ℂ)))) = d at horder
  rw [horder]
  simp

/-- Completed preparation with the degree included in the conclusion. -/
theorem exists_completed_weierstrassFactorization_natDegree
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    ∃ P : Polynomial (PowerSeries ℂ),
      ∃ U : PowerSeries (PowerSeries ℂ),
        (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization P U ∧
          P.natDegree = d := by
  obtain ⟨P, U, hfactor⟩ :=
    Germ.exists_completed_weierstrassFactorization hregular
  exact ⟨P, U, hfactor,
    Germ.natDegree_eq_of_completed_weierstrassFactorization
      hregular hfactor⟩

/-- Evaluation of a polynomial in the first coordinate with analytic
coefficients in the parameter. -/
@[expose] noncomputable def firstCoordinatePolynomialEvaluation
    (P : Polynomial (Germ 1)) : Germ 2 :=
  P.eval₂ (Germ.hyperplaneExtension 1)
    (Germ.coordinate (0 : Fin 2))

/-- Completed Taylor expansion commutes with evaluation of a polynomial in
the first coordinate. -/
theorem completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation
    (p : Polynomial (Germ 1)) :
    Germ.completedPlaneTaylorRingHom
        (Germ.firstCoordinatePolynomialEvaluation p) =
      ((p.map Germ.oneVariableTaylorRingHom :
          Polynomial (PowerSeries ℂ)) : PowerSeries (PowerSeries ℂ)) := by
  rw [Germ.firstCoordinatePolynomialEvaluation]
  rw [Polynomial.hom_eval₂]
  rw [show Germ.completedPlaneTaylorRingHom.comp
      (Germ.hyperplaneExtension 1) =
      PowerSeries.C.comp Germ.oneVariableTaylorRingHom by
    apply RingHom.ext
    intro r
    exact Germ.completedPlaneTaylorRingHom_hyperplaneExtension r]
  rw [Germ.completedPlaneTaylorRingHom_coordinate]
  rw [← Polynomial.eval₂_map]
  exact Polynomial.eval₂_C_X_eq_coe

/-- A polynomial over formal power series has analytic coefficients when it
is obtained by mapping a polynomial over one variable analytic germs. -/
def PolynomialHasAnalyticCoefficients
    (P : Polynomial (PowerSeries ℂ)) : Prop :=
  ∃ p : Polynomial (Germ 1),
    p.map Germ.oneVariableTaylorRingHom = P

/-- Analyticity of the coefficients of a polynomial is equivalent to
coefficientwise membership in the Taylor image. -/
theorem polynomialHasAnalyticCoefficients_iff
    (P : Polynomial (PowerSeries ℂ)) :
    Germ.PolynomialHasAnalyticCoefficients P ↔
      ∀ k, PowerSeries.coeff k P ∈
        Set.range Germ.oneVariableTaylorRingHom := by
  constructor
  · rintro ⟨p, rfl⟩ k
    refine ⟨p.coeff k, ?_⟩
    simp
  · intro h
    let a : ℕ → Germ 1 := fun k ↦ Classical.choose (h k)
    let p : Polynomial (Germ 1) :=
      P.sum fun k _ ↦ Polynomial.monomial k (a k)
    refine ⟨p, ?_⟩
    dsimp [p]
    rw [Polynomial.sum_def, Polynomial.map_sum]
    calc
      ∑ k ∈ P.support,
          Polynomial.map Germ.oneVariableTaylorRingHom
            (Polynomial.monomial k (a k)) =
          ∑ k ∈ P.support,
            Polynomial.monomial k (P.coeff k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Polynomial.map_monomial]
        congr 1
        simpa [a] using Classical.choose_spec (h k)
      _ = P.sum fun k c ↦ Polynomial.monomial k c := by
        rw [Polynomial.sum_def]
      _ = P := Polynomial.sum_monomial_eq P

/-- A completed formal factorization has an analytic lift when its polynomial
coefficients and its unit factor lie in the corresponding Taylor images. -/
def CompletedFactorizationHasAnalyticLift
    (P : Polynomial (PowerSeries ℂ))
    (U : PowerSeries (PowerSeries ℂ)) : Prop :=
  Germ.PolynomialHasAnalyticCoefficients P ∧
    U ∈ Set.range Germ.completedPlaneTaylorRingHom

/-- Evaluation at the origin is obtained by taking the two constant
coefficients of the completed plane Taylor series. -/
theorem constantCoeff_constantCoeff_completedPlaneTaylor (f : Germ 2) :
    PowerSeries.constantCoeff
        (PowerSeries.constantCoeff
          (Germ.completedPlaneTaylorRingHom f)) =
      Germ.valueRingHom 2 f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply
    (Germ.completedPlaneTaylorRingHom f)]
  rw [Germ.completedPlaneTaylorRingHom_coeff,
    Germ.constantCoeff_oneVariableTaylorSeries,
    Germ.value_firstCoordinateTaylorCoefficient]
  simp

/-- The completed Taylor embedding reflects analytic units. -/
theorem isUnit_of_isUnit_completedPlaneTaylor {f : Germ 2}
    (hunit : IsUnit (Germ.completedPlaneTaylorRingHom f)) :
    IsUnit f := by
  have houter : IsUnit
      (PowerSeries.constantCoeff
        (Germ.completedPlaneTaylorRingHom f)) :=
    PowerSeries.isUnit_constantCoeff _ hunit
  have hinner : IsUnit
      (PowerSeries.constantCoeff
        (PowerSeries.constantCoeff
          (Germ.completedPlaneTaylorRingHom f))) :=
    PowerSeries.isUnit_constantCoeff _ houter
  apply Germ.isUnit_of_valueRingHom_ne_zero
  rw [← Germ.constantCoeff_constantCoeff_completedPlaneTaylor f]
  exact hinner.ne_zero

/-- A completed factorization lifts to analytic germs once its polynomial
and unit factors are known to be convergent. -/
theorem lift_completed_weierstrassFactorization
    {f : Germ 2} {P : Polynomial (PowerSeries ℂ)}
    {U : PowerSeries (PowerSeries ℂ)}
    (hfactor : (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization
      P U)
    (p : Polynomial (Germ 1)) (u : Germ 2)
    (hpolynomial : (P : PowerSeries (PowerSeries ℂ)) =
      Germ.completedPlaneTaylorRingHom
        (Germ.firstCoordinatePolynomialEvaluation p))
    (hunit : U = Germ.completedPlaneTaylorRingHom u) :
    IsUnit u ∧
      f = Germ.firstCoordinatePolynomialEvaluation p * u := by
  have huCompleted : IsUnit (Germ.completedPlaneTaylorRingHom u) := by
    rw [← hunit]
    exact hfactor.isUnit
  refine ⟨Germ.isUnit_of_isUnit_completedPlaneTaylor huCompleted, ?_⟩
  apply Germ.completedPlaneTaylorRingHom_injective
  calc
    Germ.completedPlaneTaylorRingHom f =
        (P : PowerSeries (PowerSeries ℂ)) * U := hfactor.eq_mul
    _ = Germ.completedPlaneTaylorRingHom
          (Germ.firstCoordinatePolynomialEvaluation p) *
        Germ.completedPlaneTaylorRingHom u := by
      rw [hpolynomial, hunit]
    _ = Germ.completedPlaneTaylorRingHom
        (Germ.firstCoordinatePolynomialEvaluation p * u) := by
      rw [map_mul]

/-- Monicity is reflected by the injective Taylor embedding on polynomial
coefficients. -/
theorem monic_of_map_oneVariableTaylorRingHom_monic
    {p : Polynomial (Germ 1)} {P : Polynomial (PowerSeries ℂ)}
    (hp : p.map Germ.oneVariableTaylorRingHom = P) (hP : P.Monic) :
    p.Monic := by
  change p.leadingCoeff = 1
  apply Germ.oneVariableTaylorRingHom_injective
  calc
    Germ.oneVariableTaylorRingHom p.leadingCoeff =
        (p.map Germ.oneVariableTaylorRingHom).leadingCoeff := by
      rw [Polynomial.leadingCoeff_map_of_injective
        Germ.oneVariableTaylorRingHom_injective]
    _ = P.leadingCoeff := congrArg Polynomial.leadingCoeff hp
    _ = 1 := hP
    _ = Germ.oneVariableTaylorRingHom 1 :=
      (map_one Germ.oneVariableTaylorRingHom).symm

/-- The Taylor embedding maps the maximal ideal of one variable analytic
germs into the maximal ideal of formal power series. -/
theorem oneVariableTaylorRingHom_mem_maximalIdeal
    {q : Germ 1} (hq : q ∈ Germ.maximalIdeal 1) :
    Germ.oneVariableTaylorRingHom q ∈
      IsLocalRing.maximalIdeal (PowerSeries ℂ) := by
  rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker]
  rw [Germ.oneVariableTaylorRingHom_apply,
    Germ.constantCoeff_oneVariableTaylorSeries]
  exact Germ.mem_maximalIdeal_iff.mp hq

/-- An analytic Weierstrass factorization of order `d`. -/
@[expose] def HasAnalyticWeierstrassFactorizationOfOrder
    (f : Germ 2) (d : ℕ) : Prop :=
  ∃ p : Polynomial (Germ 1), ∃ u : Germ 2,
    p.Monic ∧ p.natDegree = d ∧
      (∀ k, k < d → p.coeff k ∈ Germ.maximalIdeal 1) ∧
      IsUnit u ∧
      f = Germ.firstCoordinatePolynomialEvaluation p * u

/-- A completed Weierstrass factorization whose two factors have analytic
lifts. -/
def HasLiftedCompletedWeierstrassFactorization (f : Germ 2) : Prop :=
  ∃ P : Polynomial (PowerSeries ℂ),
    ∃ U : PowerSeries (PowerSeries ℂ),
      (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization P U ∧
        Germ.CompletedFactorizationHasAnalyticLift P U

/-- Analytic lifts of the completed polynomial and unit give an analytic
factorization. -/
theorem exists_analyticFactorization_of_completedAnalyticLift
    {f : Germ 2} {P : Polynomial (PowerSeries ℂ)}
    {U : PowerSeries (PowerSeries ℂ)}
    (hfactor : (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization
      P U)
    (hlift : Germ.CompletedFactorizationHasAnalyticLift P U) :
    ∃ p : Polynomial (Germ 1), ∃ u : Germ 2,
      p.map Germ.oneVariableTaylorRingHom = P ∧
        Germ.completedPlaneTaylorRingHom u = U ∧
        IsUnit u ∧
        f = Germ.firstCoordinatePolynomialEvaluation p * u := by
  rcases hlift with ⟨⟨p, hp⟩, ⟨u, hu⟩⟩
  have hpolynomial : (P : PowerSeries (PowerSeries ℂ)) =
      Germ.completedPlaneTaylorRingHom
        (Germ.firstCoordinatePolynomialEvaluation p) := by
    rw [Germ.completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation,
      hp]
  have hlifted := Germ.lift_completed_weierstrassFactorization hfactor p u
    hpolynomial hu.symm
  exact ⟨p, u, hp, hu, hlifted.1, hlifted.2⟩

/-- A lifted completed factorization of a regular germ gives an analytic
Weierstrass factorization of the same order. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_of_liftedCompleted
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d)
    (hlifted : Germ.HasLiftedCompletedWeierstrassFactorization f) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f d := by
  rcases hlifted with ⟨P, U, hfactor, hlift⟩
  obtain ⟨p, u, hp, hu, hunit, heq⟩ :=
    Germ.exists_analyticFactorization_of_completedAnalyticLift hfactor hlift
  have hpMonic : p.Monic :=
    Germ.monic_of_map_oneVariableTaylorRingHom_monic hp
      hfactor.isDistinguishedAt.monic
  have hpDegree : p.natDegree = d := by
    rw [← Germ.natDegree_eq_of_completed_weierstrassFactorization
      hregular hfactor]
    rw [← hp]
    exact (Polynomial.natDegree_map_eq_of_injective
      Germ.oneVariableTaylorRingHom_injective p).symm
  refine ⟨p, u, hpMonic, hpDegree, ?_, hunit, heq⟩
  intro k hk
  rw [Germ.mem_maximalIdeal_iff]
  rw [← Germ.constantCoeff_oneVariableTaylorSeries]
  have hformal : P.coeff k ∈
      IsLocalRing.maximalIdeal (PowerSeries ℂ) :=
    hfactor.isDistinguishedAt.toIsWeaklyEisensteinAt.mem (by
      rw [Germ.natDegree_eq_of_completed_weierstrassFactorization
        hregular hfactor]
      exact hk)
  rw [← hp, Polynomial.coeff_map,
    ← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker] at hformal
  exact hformal

/-- An analytic Weierstrass factorization induces a completed factorization
whose factors have analytic lifts. -/
theorem hasLiftedCompletedWeierstrassFactorization_of_analytic
    {d : ℕ} {f : Germ 2}
    (h : Germ.HasAnalyticWeierstrassFactorizationOfOrder f d) :
    Germ.HasLiftedCompletedWeierstrassFactorization f := by
  rcases h with ⟨p, u, hpMonic, hpDegree, hpCoeff, hu, heq⟩
  let P := p.map Germ.oneVariableTaylorRingHom
  let U := Germ.completedPlaneTaylorRingHom u
  refine ⟨P, U, ?_, ⟨⟨p, rfl⟩, ⟨u, rfl⟩⟩⟩
  refine ⟨⟨⟨?_⟩, hpMonic.map Germ.oneVariableTaylorRingHom⟩, ?_, ?_⟩
  · intro k hk
    change (p.map Germ.oneVariableTaylorRingHom).coeff k ∈ _
    rw [Polynomial.coeff_map]
    apply Germ.oneVariableTaylorRingHom_mem_maximalIdeal
    apply hpCoeff k
    change k < (p.map Germ.oneVariableTaylorRingHom).natDegree at hk
    rw [Polynomial.natDegree_map_eq_of_injective
      Germ.oneVariableTaylorRingHom_injective] at hk
    simpa [hpDegree] using hk
  · exact hu.map Germ.completedPlaneTaylorRingHom
  · rw [heq, map_mul,
      Germ.completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation]

/-- For a regular germ, the analytic preparation theorem is equivalent to
analytic liftability of one completed preparation. -/
theorem hasLiftedCompletedWeierstrassFactorization_iff_analytic
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    Germ.HasLiftedCompletedWeierstrassFactorization f ↔
      Germ.HasAnalyticWeierstrassFactorizationOfOrder f d := by
  constructor
  · exact
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_of_liftedCompleted
        hregular
  · exact Germ.hasLiftedCompletedWeierstrassFactorization_of_analytic

/-- The analytic lift condition on completed factors can be stated using
positive Taylor radius for every polynomial coefficient. -/
theorem completedFactorizationHasAnalyticLift_iff
    (P : Polynomial (PowerSeries ℂ))
    (U : PowerSeries (PowerSeries ℂ)) :
    Germ.CompletedFactorizationHasAnalyticLift P U ↔
      (∀ k, Germ.HasPositiveTaylorRadius (PowerSeries.coeff k P)) ∧
        U ∈ Set.range Germ.completedPlaneTaylorRingHom := by
  rw [Germ.CompletedFactorizationHasAnalyticLift,
    Germ.polynomialHasAnalyticCoefficients_iff]
  constructor
  · rintro ⟨hP, hU⟩
    exact ⟨fun k ↦
      (Germ.hasPositiveTaylorRadius_iff_mem_range_oneVariableTaylorRingHom
        _).2 (hP k), hU⟩
  · rintro ⟨hP, hU⟩
    exact ⟨fun k ↦
      (Germ.hasPositiveTaylorRadius_iff_mem_range_oneVariableTaylorRingHom
        _).1 (hP k), hU⟩

/-- This proposition is the remaining image closure statement for analytic
Weierstrass preparation at order `d`. -/
def CompletedWeierstrassImageClosureAtOrder (d : ℕ) : Prop :=
  ∀ f : Germ 2,
    Germ.IsRegularInFirstCoordinateOfOrder f d →
      ∃ P : Polynomial (PowerSeries ℂ),
        ∃ U : PowerSeries (PowerSeries ℂ),
          (Germ.completedPlaneTaylorRingHom f).IsWeierstrassFactorization
              P U ∧
            (∀ k,
              Germ.HasPositiveTaylorRadius (PowerSeries.coeff k P)) ∧
            U ∈ Set.range Germ.completedPlaneTaylorRingHom

/-- The image closure statement at order `d` implies analytic Weierstrass
preparation at that order. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_of_imageClosure
    {d : ℕ} (hclosure : Germ.CompletedWeierstrassImageClosureAtOrder d)
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f d := by
  obtain ⟨P, U, hfactor, hP, hU⟩ := hclosure f hregular
  apply Germ.hasAnalyticWeierstrassFactorizationOfOrder_of_liftedCompleted
    hregular
  refine ⟨P, U, hfactor, ?_⟩
  exact (Germ.completedFactorizationHasAnalyticLift_iff P U).2 ⟨hP, hU⟩

/-- The completed image closure statement is equivalent to analytic
Weierstrass preparation for every germ regular of order `d`. -/
theorem completedWeierstrassImageClosureAtOrder_iff
    (d : ℕ) :
    Germ.CompletedWeierstrassImageClosureAtOrder d ↔
      ∀ f : Germ 2,
        Germ.IsRegularInFirstCoordinateOfOrder f d →
          Germ.HasAnalyticWeierstrassFactorizationOfOrder f d := by
  constructor
  · intro hclosure f hregular
    exact Germ.hasAnalyticWeierstrassFactorizationOfOrder_of_imageClosure
      hclosure hregular
  · intro hanalytic f hregular
    have hlifted :=
      Germ.hasLiftedCompletedWeierstrassFactorization_of_analytic
        (hanalytic f hregular)
    rcases hlifted with ⟨P, U, hfactor, hlift⟩
    have hclosure :=
      (Germ.completedFactorizationHasAnalyticLift_iff P U).1 hlift
    exact ⟨P, U, hfactor, hclosure.1, hclosure.2⟩

end Germ

end OnLeConjecture.Analytic
