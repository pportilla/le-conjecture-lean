/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.EvenBranchIntersection
public import OnLeConjecture.Analytic.DVRCokernel

/-!
# The quadratic remainder module

Reduction modulo `x²+yᵏ` identifies the plane analytic germ ring with a free
module of rank two over the one variable analytic germ ring. This file
constructs that identification from the analytic quadratic decomposition.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

namespace Germ

/-- The unique coefficient pair in the quadratic base decomposition. -/
@[expose]
noncomputable def quadraticBaseCoefficientPair
    (k : ℕ) (hk : 1 ≤ k) (f : Germ 2) : Germ 2 × Germ 2 :=
  Classical.choose (existsUnique_quadraticBase_decomposition k hk f)

theorem quadraticBaseCoefficientPair_spec
    (k : ℕ) (hk : 1 ≤ k) (f : Germ 2) :
    f = quadraticBaseSubstitutionAlgHom k hk
          (quadraticBaseCoefficientPair k hk f).1 +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk f).2 :=
  (Classical.choose_spec
    (existsUnique_quadraticBase_decomposition k hk f)).1

theorem quadraticBaseCoefficientPair_eq
    (k : ℕ) (hk : 1 ≤ k) (f A B : Germ 2)
    (h : f = quadraticBaseSubstitutionAlgHom k hk A +
      Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk B) :
    quadraticBaseCoefficientPair k hk f = (A, B) := by
  exact ((Classical.choose_spec
    (existsUnique_quadraticBase_decomposition k hk f)).2 (A, B) h).symm

theorem quadraticBaseCoefficientPair_zero
    (k : ℕ) (hk : 1 ≤ k) :
    quadraticBaseCoefficientPair k hk 0 = 0 := by
  apply quadraticBaseCoefficientPair_eq
  simp

theorem quadraticBaseCoefficientPair_add
    (k : ℕ) (hk : 1 ≤ k) (f g : Germ 2) :
    quadraticBaseCoefficientPair k hk (f + g) =
      quadraticBaseCoefficientPair k hk f +
        quadraticBaseCoefficientPair k hk g := by
  apply quadraticBaseCoefficientPair_eq
  calc
    f + g =
        (quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk f).1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (quadraticBaseCoefficientPair k hk f).2) +
        (quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk g).1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (quadraticBaseCoefficientPair k hk g).2) := by
      exact congrArg₂ (fun q r : Germ 2 ↦ q + r)
        (quadraticBaseCoefficientPair_spec k hk f)
        (quadraticBaseCoefficientPair_spec k hk g)
    _ = quadraticBaseSubstitutionAlgHom k hk
          ((quadraticBaseCoefficientPair k hk f).1 +
            (quadraticBaseCoefficientPair k hk g).1) +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            ((quadraticBaseCoefficientPair k hk f).2 +
              (quadraticBaseCoefficientPair k hk g).2) := by
      rw [map_add, map_add]
      ring

theorem quadraticBaseCoefficientPair_smul
    (k : ℕ) (hk : 1 ≤ k) (c : ℂ) (f : Germ 2) :
    quadraticBaseCoefficientPair k hk (c • f) =
      c • quadraticBaseCoefficientPair k hk f := by
  apply quadraticBaseCoefficientPair_eq
  calc
    c • f = c •
        (quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk f).1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (quadraticBaseCoefficientPair k hk f).2) := by
      exact congrArg (fun q : Germ 2 ↦ c • q)
        (quadraticBaseCoefficientPair_spec k hk f)
    _ = quadraticBaseSubstitutionAlgHom k hk
          (c • (quadraticBaseCoefficientPair k hk f).1) +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            (c • (quadraticBaseCoefficientPair k hk f).2) := by
      rw [map_smul, map_smul]
      rw [smul_add]
      congr 1
      rw [Algebra.smul_def, Algebra.smul_def]
      ring

/-- The quadratic coefficient pair as a complex linear map. -/
@[expose]
noncomputable def quadraticBaseCoefficientPairLinear
    (k : ℕ) (hk : 1 ≤ k) : Germ 2 →ₗ[ℂ] Germ 2 × Germ 2 where
  toFun := quadraticBaseCoefficientPair k hk
  map_add' := quadraticBaseCoefficientPair_add k hk
  map_smul' := quadraticBaseCoefficientPair_smul k hk

/-- Restriction of the two quadratic coefficients to the divisor
`x²+yᵏ=0`. -/
@[expose]
noncomputable def quadraticBaseRemainder
    (k : ℕ) (hk : 1 ≤ k) : Germ 2 →ₗ[ℂ] (Fin 2 → Germ 1) where
  toFun f := ![
    Germ.hyperplaneRestrictionAlgHom 1
      (quadraticBaseCoefficientPair k hk f).1,
    Germ.hyperplaneRestrictionAlgHom 1
      (quadraticBaseCoefficientPair k hk f).2]
  map_add' f g := by
    rw [quadraticBaseCoefficientPair_add]
    ext i
    fin_cases i <;> simp
  map_smul' c f := by
    rw [quadraticBaseCoefficientPair_smul]
    ext i
    fin_cases i <;> simp

@[simp]
theorem quadraticBaseRemainder_apply_zero
    (k : ℕ) (hk : 1 ≤ k) (f : Germ 2) :
    quadraticBaseRemainder k hk f 0 =
      Germ.hyperplaneRestriction 1
        (quadraticBaseCoefficientPair k hk f).1 :=
  rfl

@[simp]
theorem quadraticBaseRemainder_apply_one
    (k : ℕ) (hk : 1 ≤ k) (f : Germ 2) :
    quadraticBaseRemainder k hk f 1 =
      Germ.hyperplaneRestriction 1
        (quadraticBaseCoefficientPair k hk f).2 :=
  rfl

/-- The equation used as the first coordinate of the quadratic base map. -/
@[expose]
noncomputable def quadraticBaseEquation (k : ℕ) : Germ 2 :=
  Germ.coordinate (0 : Fin 2) ^ 2 +
    Germ.coordinate (1 : Fin 2) ^ k

theorem quadraticBaseSubstitution_coordinate_zero
    (k : ℕ) (hk : 1 ≤ k) :
    quadraticBaseSubstitutionAlgHom k hk
        (Germ.coordinate (0 : Fin 2)) =
      quadraticBaseEquation k := by
  exact quadraticBaseSubstitutionAlgHom_coordinate_zero k hk

/-- The quadratic remainder map is onto. -/
theorem quadraticBaseRemainder_surjective
    (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (quadraticBaseRemainder k hk) := by
  intro v
  let A := Germ.hyperplaneExtension 1 (v 0)
  let B := Germ.hyperplaneExtension 1 (v 1)
  let f := quadraticBaseSubstitutionAlgHom k hk A +
    Germ.coordinate (0 : Fin 2) *
      quadraticBaseSubstitutionAlgHom k hk B
  refine ⟨f, ?_⟩
  have hcoeff : quadraticBaseCoefficientPair k hk f = (A, B) := by
    exact quadraticBaseCoefficientPair_eq k hk f A B rfl
  apply funext
  intro i
  fin_cases i
  · change quadraticBaseRemainder k hk f 0 = v 0
    rw [quadraticBaseRemainder_apply_zero, hcoeff]
    exact DFunLike.congr_fun (Germ.hyperplaneRestriction_comp_extension 1) (v 0)
  · change quadraticBaseRemainder k hk f 1 = v 1
    rw [quadraticBaseRemainder_apply_one, hcoeff]
    exact DFunLike.congr_fun (Germ.hyperplaneRestriction_comp_extension 1) (v 1)

private theorem mem_span_coordinate_zero_of_restriction_eq_zero
    (A : Germ 2) (hA : Germ.hyperplaneRestriction 1 A = 0) :
    A ∈ Ideal.span {Germ.coordinate (0 : Fin 2)} := by
  rw [← Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero]
  exact hA

/-- The kernel of the quadratic remainder map is the complex subspace
underlying the principal ideal generated by `x²+yᵏ`. -/
theorem ker_quadraticBaseRemainder
    (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.ker (quadraticBaseRemainder k hk) =
      (Ideal.span {quadraticBaseEquation k}).restrictScalars ℂ := by
  ext f
  constructor
  · intro hf
    rw [LinearMap.mem_ker] at hf
    let p := quadraticBaseCoefficientPair k hk f
    have hfirst : Germ.hyperplaneRestriction 1 p.1 = 0 := by
      have h := congrFun hf (0 : Fin 2)
      simpa [p] using h
    have hsecond : Germ.hyperplaneRestriction 1 p.2 = 0 := by
      have h := congrFun hf (1 : Fin 2)
      simpa [p] using h
    have hfirstMem :=
      mem_span_coordinate_zero_of_restriction_eq_zero p.1 hfirst
    have hsecondMem :=
      mem_span_coordinate_zero_of_restriction_eq_zero p.2 hsecond
    rw [Ideal.mem_span_singleton'] at hfirstMem hsecondMem
    rcases hfirstMem with ⟨C, hC⟩
    rcases hsecondMem with ⟨D, hD⟩
    change f ∈ Ideal.span {quadraticBaseEquation k}
    rw [Ideal.mem_span_singleton']
    refine ⟨quadraticBaseSubstitutionAlgHom k hk C +
      Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk D, ?_⟩
    calc
      (quadraticBaseSubstitutionAlgHom k hk C +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk D) *
          quadraticBaseEquation k =
        quadraticBaseSubstitutionAlgHom k hk
            (C * Germ.coordinate (0 : Fin 2)) +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (D * Germ.coordinate (0 : Fin 2)) := by
        rw [← quadraticBaseSubstitution_coordinate_zero k hk,
          map_mul, map_mul]
        ring
      _ = quadraticBaseSubstitutionAlgHom k hk p.1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk p.2 := by
        rw [hC, hD]
      _ = f := (quadraticBaseCoefficientPair_spec k hk f).symm
  · intro hf
    change f ∈ Ideal.span {quadraticBaseEquation k} at hf
    rw [Ideal.mem_span_singleton'] at hf
    rcases hf with ⟨q, hq⟩
    let p := quadraticBaseCoefficientPair k hk q
    have hqDecomp := quadraticBaseCoefficientPair_spec k hk q
    have hfDecomp :
        f = quadraticBaseSubstitutionAlgHom k hk
              (Germ.coordinate (0 : Fin 2) * p.1) +
            Germ.coordinate (0 : Fin 2) *
              quadraticBaseSubstitutionAlgHom k hk
                (Germ.coordinate (0 : Fin 2) * p.2) := by
      rw [← hq]
      rw [hqDecomp]
      rw [map_mul, map_mul,
        quadraticBaseSubstitution_coordinate_zero]
      ring
    have hcoeff : quadraticBaseCoefficientPair k hk f =
        (Germ.coordinate (0 : Fin 2) * p.1,
          Germ.coordinate (0 : Fin 2) * p.2) :=
      quadraticBaseCoefficientPair_eq k hk f _ _ hfDecomp
    rw [LinearMap.mem_ker]
    apply funext
    intro i
    fin_cases i
    · change quadraticBaseRemainder k hk f 0 = (0 : Fin 2 → Germ 1) 0
      rw [quadraticBaseRemainder_apply_zero, hcoeff]
      simp
    · change quadraticBaseRemainder k hk f 1 = (0 : Fin 2 → Germ 1) 1
      rw [quadraticBaseRemainder_apply_one, hcoeff]
      simp

end Germ

end OnLeConjecture.DTwo
