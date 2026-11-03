/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.EvenOuterConvergence
public import OnLeConjecture.Analytic.JacobianPullback

/-!
# Analytic decomposition over a quadratic plane map

For a positive integer `k`, this file identifies the invariant analytic
subring associated with the map

`(x,y) ↦ (x²+yᵏ,y)`.

Every plane analytic germ then has a unique expression

`A(x²+yᵏ,y) + x B(x²+yᵏ,y)`.
-/

public section

namespace OnLeConjecture.DTwo

open Filter
open scoped Topology
open OnLeConjecture.Analytic

namespace Germ

/-- Translation of the first coordinate by the `k`th power of the second
coordinate. -/
@[expose]
noncomputable def quadraticBaseShiftMap (k : ℕ) (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 + z 1 ^ k) (fun j ↦ z j.succ) i

/-- Translation of the first coordinate by the negative of the `k`th power
of the second coordinate. -/
@[expose]
noncomputable def quadraticBaseShiftInverseMap
    (k : ℕ) (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 - z 1 ^ k) (fun j ↦ z j.succ) i

@[simp]
theorem quadraticBaseShiftMap_apply_zero (k : ℕ) (z : Source 2) :
    quadraticBaseShiftMap k z 0 = z 0 + z 1 ^ k := by
  simp [quadraticBaseShiftMap]

@[simp]
theorem quadraticBaseShiftMap_apply_one (k : ℕ) (z : Source 2) :
    quadraticBaseShiftMap k z 1 = z 1 := by
  change Fin.cases (z 0 + z 1 ^ k) (fun j : Fin 1 ↦ z j.succ) 1 = z 1
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rfl

@[simp]
theorem quadraticBaseShiftInverseMap_apply_zero (k : ℕ) (z : Source 2) :
    quadraticBaseShiftInverseMap k z 0 = z 0 - z 1 ^ k := by
  simp [quadraticBaseShiftInverseMap]

@[simp]
theorem quadraticBaseShiftInverseMap_apply_one (k : ℕ) (z : Source 2) :
    quadraticBaseShiftInverseMap k z 1 = z 1 := by
  change Fin.cases (z 0 - z 1 ^ k) (fun j : Fin 1 ↦ z j.succ) 1 = z 1
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rfl

theorem quadraticBaseShiftMap_analyticAt (k : ℕ) :
    AnalyticAt ℂ (quadraticBaseShiftMap k) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).add
        (((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0).pow k)
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

theorem quadraticBaseShiftInverseMap_analyticAt (k : ℕ) :
    AnalyticAt ℂ (quadraticBaseShiftInverseMap k) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).sub
        (((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0).pow k)
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

@[simp]
theorem quadraticBaseShiftMap_zero {k : ℕ} (hk : 1 ≤ k) :
    quadraticBaseShiftMap k (0 : Source 2) = 0 := by
  ext i
  fin_cases i <;> simp [zero_pow (by omega : k ≠ 0)]

@[simp]
theorem quadraticBaseShiftInverseMap_zero {k : ℕ} (hk : 1 ≤ k) :
    quadraticBaseShiftInverseMap k (0 : Source 2) = 0 := by
  ext i
  fin_cases i <;> simp [zero_pow (by omega : k ≠ 0)]

@[simp]
theorem quadraticBaseShiftMap_inverse (k : ℕ) (z : Source 2) :
    quadraticBaseShiftMap k (quadraticBaseShiftInverseMap k z) = z := by
  ext i
  fin_cases i <;> simp

@[simp]
theorem quadraticBaseShiftInverseMap_shift (k : ℕ) (z : Source 2) :
    quadraticBaseShiftInverseMap k (quadraticBaseShiftMap k z) = z := by
  ext i
  fin_cases i <;> simp

/-- The pointed germ represented by translation of the first coordinate by
the `k`th power of the second coordinate. -/
@[expose]
noncomputable def quadraticBaseShiftGerm (k : ℕ) (hk : 1 ≤ k) :
    PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (quadraticBaseShiftMap k)
    (quadraticBaseShiftMap_analyticAt k) (quadraticBaseShiftMap_zero hk)

/-- The inverse pointed germ for `quadraticBaseShiftGerm`. -/
@[expose]
noncomputable def quadraticBaseShiftInverseGerm (k : ℕ) (hk : 1 ≤ k) :
    PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (quadraticBaseShiftInverseMap k)
    (quadraticBaseShiftInverseMap_analyticAt k)
    (quadraticBaseShiftInverseMap_zero hk)

@[simp]
theorem quadraticBaseShiftGerm_comp_inverse (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseShiftGerm k hk).comp
        (quadraticBaseShiftInverseGerm k hk) =
      PointedMapGerm.identity 2 := by
  rw [quadraticBaseShiftGerm, quadraticBaseShiftInverseGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ quadraticBaseShiftMap_inverse k z

@[simp]
theorem quadraticBaseShiftInverseGerm_comp (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseShiftInverseGerm k hk).comp
        (quadraticBaseShiftGerm k hk) =
      PointedMapGerm.identity 2 := by
  rw [quadraticBaseShiftGerm, quadraticBaseShiftInverseGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    quadraticBaseShiftInverseMap_shift k z

/-- Translation of the first coordinate by a power of the second coordinate
as an analytic equivalence. -/
@[expose]
noncomputable def quadraticBaseShiftEquiv (k : ℕ) (hk : 1 ≤ k) :
    PointedEquivGerm 2 where
  forward := quadraticBaseShiftGerm k hk
  inverse := quadraticBaseShiftInverseGerm k hk
  forward_inverse := quadraticBaseShiftGerm_comp_inverse k hk
  inverse_forward := quadraticBaseShiftInverseGerm_comp k hk

/-- The pointed plane map `(x,y) ↦ (x²+yᵏ,y)`. -/
@[expose]
noncomputable def quadraticBaseMapGerm (k : ℕ) (hk : 1 ≤ k) :
    PointedMapGerm 2 2 :=
  (quadraticBaseShiftGerm k hk).comp Germ.quadraticMapGerm

/-- Substitution `(u,y) = (x²+yᵏ,y)` on analytic plane germs. -/
@[expose]
noncomputable def quadraticBaseSubstitutionAlgHom (k : ℕ) (hk : 1 ≤ k) :
    Germ 2 →ₐ[ℂ] Germ 2 :=
  Germ.quadraticSubstitutionAlgHom.comp
    (quadraticBaseShiftEquiv k hk).pullbackAlgEquiv.toAlgHom

theorem quadraticBaseSubstitutionAlgHom_apply
    (k : ℕ) (hk : 1 ≤ k) (q : Germ 2) :
    quadraticBaseSubstitutionAlgHom k hk q =
      Germ.compPointed q (quadraticBaseMapGerm k hk) := by
  change
    Germ.quadraticMapGerm.pullbackRingHom
        ((quadraticBaseShiftGerm k hk).pullbackRingHom q) =
      (quadraticBaseMapGerm k hk).pullbackRingHom q
  rw [quadraticBaseMapGerm, PointedMapGerm.pullbackRingHom_comp]
  rfl

@[simp]
theorem quadraticBaseShiftEquiv_coordinate_zero (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseShiftEquiv k hk).pullbackAlgEquiv
        (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) + Germ.coordinate (1 : Fin 2) ^ k := by
  rw [PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem quadraticBaseShiftEquiv_coordinate_one (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseShiftEquiv k hk).pullbackAlgEquiv
        (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem quadraticBaseSubstitutionAlgHom_coordinate_zero
    (k : ℕ) (hk : 1 ≤ k) :
    quadraticBaseSubstitutionAlgHom k hk (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.coordinate (1 : Fin 2) ^ k := by
  rw [quadraticBaseSubstitutionAlgHom, AlgHom.comp_apply]
  change Germ.quadraticSubstitutionAlgHom
      ((quadraticBaseShiftEquiv k hk).pullbackAlgEquiv
        (Germ.coordinate (0 : Fin 2))) = _
  rw [quadraticBaseShiftEquiv_coordinate_zero]
  simp

@[simp]
theorem quadraticBaseSubstitutionAlgHom_coordinate_one
    (k : ℕ) (hk : 1 ≤ k) :
    quadraticBaseSubstitutionAlgHom k hk (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [quadraticBaseSubstitutionAlgHom, AlgHom.comp_apply]
  change Germ.quadraticSubstitutionAlgHom
      ((quadraticBaseShiftEquiv k hk).pullbackAlgEquiv
        (Germ.coordinate (1 : Fin 2))) = _
  rw [quadraticBaseShiftEquiv_coordinate_one]
  simp

@[simp]
theorem quadraticBaseMapGerm_component_zero
    (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseMapGerm k hk).1.component (0 : Fin 2) =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.coordinate (1 : Fin 2) ^ k := by
  rw [← PointedMapGerm.pullback_coordinate]
  change Germ.compPointed (Germ.coordinate (0 : Fin 2))
      (quadraticBaseMapGerm k hk) = _
  rw [← quadraticBaseSubstitutionAlgHom_apply]
  exact quadraticBaseSubstitutionAlgHom_coordinate_zero k hk

@[simp]
theorem quadraticBaseMapGerm_component_one
    (k : ℕ) (hk : 1 ≤ k) :
    (quadraticBaseMapGerm k hk).1.component (1 : Fin 2) =
      Germ.coordinate (1 : Fin 2) := by
  rw [← PointedMapGerm.pullback_coordinate]
  change Germ.compPointed (Germ.coordinate (1 : Fin 2))
      (quadraticBaseMapGerm k hk) = _
  rw [← quadraticBaseSubstitutionAlgHom_apply]
  exact quadraticBaseSubstitutionAlgHom_coordinate_one k hk

theorem quadraticBaseMapGerm_coordinateJacobian
    (k : ℕ) (hk : 1 ≤ k) :
    Germ.coordinateJacobian (quadraticBaseMapGerm k hk) =
      2 * Germ.coordinate (0 : Fin 2) := by
  rw [Germ.coordinateJacobian_eq,
    quadraticBaseMapGerm_component_zero,
    quadraticBaseMapGerm_component_one]
  simp only [Germ.partialDerivative_add, Germ.partialDerivative_pow,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_coordinate_ne (by decide :
      (0 : Fin 2) ≠ (1 : Fin 2)),
    Germ.partialDerivative_coordinate_ne (by decide :
      (1 : Fin 2) ≠ (0 : Fin 2))]
  simp

/-- The Jacobian of `x²+yᵏ` with a germ in the analytic base subring is
twice `x` times the pullback of its derivative in `y`. -/
theorem jacobian_quadraticBaseSubstitution
    (k : ℕ) (hk : 1 ≤ k) (q : Germ 2) :
    Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (quadraticBaseSubstitutionAlgHom k hk q) =
      2 * Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk
          (Germ.partialDerivative (1 : Fin 2) q) := by
  have h := Germ.jacobian_compPointed
    (Germ.coordinate (0 : Fin 2)) q (quadraticBaseMapGerm k hk)
  rw [← quadraticBaseSubstitutionAlgHom_apply,
    ← quadraticBaseSubstitutionAlgHom_apply,
    ← quadraticBaseSubstitutionAlgHom_apply,
    Germ.jacobian_coordinate_zero_left,
    quadraticBaseMapGerm_coordinateJacobian] at h
  rw [quadraticBaseSubstitutionAlgHom_coordinate_zero] at h
  calc
    Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (quadraticBaseSubstitutionAlgHom k hk q) =
        quadraticBaseSubstitutionAlgHom k hk
            (Germ.partialDerivative (1 : Fin 2) q) *
          (2 * Germ.coordinate (0 : Fin 2)) := h
    _ = 2 * Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk
          (Germ.partialDerivative (1 : Fin 2) q) := by ring

/-- The Jacobian of `x²+yᵏ` with `x` is the negative derivative of `yᵏ`. -/
theorem jacobian_quadraticBase_coordinate_zero
    (k : ℕ) :
    Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.coordinate (0 : Fin 2)) =
      -(k • Germ.coordinate (1 : Fin 2) ^ (k - 1)) := by
  rw [Germ.jacobian_eq]
  simp only [Germ.partialDerivative_add, Germ.partialDerivative_pow,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_coordinate_ne (by decide :
      (0 : Fin 2) ≠ (1 : Fin 2)),
    Germ.partialDerivative_coordinate_ne (by decide :
      (1 : Fin 2) ≠ (0 : Fin 2))]
  simp

/-- The Jacobian identity used to separate the two free summands in the
quadratic coefficient recurrence. -/
theorem jacobian_quadraticBase_decomposition
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2) :
    Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk B) =
      2 * Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            (Germ.partialDerivative (1 : Fin 2) A) +
        2 * Germ.coordinate (0 : Fin 2) ^ 2 *
          quadraticBaseSubstitutionAlgHom k hk
            (Germ.partialDerivative (1 : Fin 2) B) -
        (k • Germ.coordinate (1 : Fin 2) ^ (k - 1)) *
          quadraticBaseSubstitutionAlgHom k hk B := by
  rw [Germ.jacobian_add_right, Germ.jacobian_mul_right,
    jacobian_quadraticBaseSubstitution,
    jacobian_quadraticBaseSubstitution,
    jacobian_quadraticBase_coordinate_zero]
  ring

/-- The coefficient differential in the analytic base coordinates `(g,y)`. -/
@[expose]
noncomputable def quadraticBaseCoefficientDifferential
    (k : ℕ) (B : Germ 2) : Germ 2 :=
  2 * (Germ.coordinate (0 : Fin 2) -
      Germ.coordinate (1 : Fin 2) ^ k) *
        Germ.partialDerivative (1 : Fin 2) B -
    (k • Germ.coordinate (1 : Fin 2) ^ (k - 1)) * B

/-- The Jacobian of a quadratic base decomposition is the sum of its odd
free summand and the pullback of the coefficient differential. -/
theorem jacobian_quadraticBase_decomposition_eq_coefficientDifferential
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2) :
    Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk B) =
      Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            (2 * Germ.partialDerivative (1 : Fin 2) A) +
        quadraticBaseSubstitutionAlgHom k hk
          (quadraticBaseCoefficientDifferential k B) := by
  rw [jacobian_quadraticBase_decomposition]
  simp only [quadraticBaseCoefficientDifferential, map_sub, map_mul,
    map_nsmul, map_pow, map_ofNat,
    quadraticBaseSubstitutionAlgHom_coordinate_zero,
    quadraticBaseSubstitutionAlgHom_coordinate_one]
  ring

theorem quadraticBaseSubstitutionAlgHom_injective
    (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (quadraticBaseSubstitutionAlgHom k hk) := by
  intro a b hab
  apply (quadraticBaseShiftEquiv k hk).pullbackAlgEquiv.injective
  apply Germ.quadraticSubstitutionAlgHom_injective
  exact hab

/-- Every plane analytic germ has a unique expression over the analytic
subring generated by `x²+yᵏ` and `y`, with basis `1,x`. -/
theorem existsUnique_quadraticBase_decomposition
    (k : ℕ) (hk : 1 ≤ k) (f : Germ 2) :
    ∃! p : Germ 2 × Germ 2,
      f = quadraticBaseSubstitutionAlgHom k hk p.1 +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk p.2 := by
  obtain ⟨p, hp, hpUnique⟩ :=
    Germ.existsUnique_quadratic_decomposition
      Germ.quadraticInvariantDescent_of_convergent_compression f
  let e := quadraticBaseShiftEquiv k hk
  let a : Germ 2 := e.pullbackAlgEquiv.symm p.1
  let b : Germ 2 := e.pullbackAlgEquiv.symm p.2
  refine ⟨⟨a, b⟩, ?_, ?_⟩
  · simpa [quadraticBaseSubstitutionAlgHom, e, a, b] using hp
  · intro q hq
    rcases q with ⟨a', b'⟩
    have hdecomposition :
        f = Germ.quadraticSubstitutionAlgHom
              (e.pullbackAlgEquiv a') +
            Germ.coordinate (0 : Fin 2) *
              Germ.quadraticSubstitutionAlgHom
                (e.pullbackAlgEquiv b') := by
      simpa [quadraticBaseSubstitutionAlgHom, e] using hq
    have hpair := hpUnique
      ⟨e.pullbackAlgEquiv a', e.pullbackAlgEquiv b'⟩ hdecomposition
    apply Prod.ext
    · change a' = a
      have hfirst := congrArg Prod.fst hpair
      change e.pullbackAlgEquiv a' = p.1 at hfirst
      rw [← e.pullbackAlgEquiv.apply_symm_apply p.1] at hfirst
      exact e.pullbackAlgEquiv.injective hfirst
    · change b' = b
      have hsecond := congrArg Prod.snd hpair
      change e.pullbackAlgEquiv b' = p.2 at hsecond
      rw [← e.pullbackAlgEquiv.apply_symm_apply p.2] at hsecond
      exact e.pullbackAlgEquiv.injective hsecond

/-- The two coefficients in a quadratic base decomposition are unique. -/
theorem quadraticBase_decomposition_unique
    (k : ℕ) (hk : 1 ≤ k) {f A B A' B' : Germ 2}
    (h : f = quadraticBaseSubstitutionAlgHom k hk A +
      Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk B)
    (h' : f = quadraticBaseSubstitutionAlgHom k hk A' +
      Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk B') :
    A = A' ∧ B = B' := by
  let e := quadraticBaseShiftEquiv k hk
  have hdecomposition :
      f = Germ.quadraticSubstitutionAlgHom (e.pullbackAlgEquiv A) +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticSubstitutionAlgHom (e.pullbackAlgEquiv B) := by
    simpa [quadraticBaseSubstitutionAlgHom, e] using h
  have hdecomposition' :
      f = Germ.quadraticSubstitutionAlgHom (e.pullbackAlgEquiv A') +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticSubstitutionAlgHom (e.pullbackAlgEquiv B') := by
    simpa [quadraticBaseSubstitutionAlgHom, e] using h'
  obtain ⟨hA, hB⟩ :=
    Germ.quadratic_decomposition_unique hdecomposition hdecomposition'
  exact ⟨e.pullbackAlgEquiv.injective hA,
    e.pullbackAlgEquiv.injective hB⟩

/-- Divisibility of the Jacobian by `y^(m-1)` forces the corresponding
divisibilities in both coefficients of the free decomposition. -/
theorem coefficient_divisibilities_of_jacobian
    (k m : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk B)) :
    Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.partialDerivative (1 : Fin 2) A ∧
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        quadraticBaseCoefficientDifferential k B := by
  let y : Germ 2 := Germ.coordinate (1 : Fin 2)
  let J : Germ 2 := Germ.jacobian
    (Germ.coordinate (0 : Fin 2) ^ 2 +
      Germ.coordinate (1 : Fin 2) ^ k)
    (quadraticBaseSubstitutionAlgHom k hk A +
      Germ.coordinate (0 : Fin 2) *
        quadraticBaseSubstitutionAlgHom k hk B)
  obtain ⟨Q, hQ⟩ := hdiv
  obtain ⟨p, hp, _hpUnique⟩ :=
    existsUnique_quadraticBase_decomposition k hk Q
  rcases p with ⟨C, E⟩
  have hyPower :
      quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1)) =
        y ^ (m - 1) := by
    simp [y]
  have hleft :
      J = quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientDifferential k B) +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (2 * Germ.partialDerivative (1 : Fin 2) A) := by
    dsimp only [J]
    rw [jacobian_quadraticBase_decomposition_eq_coefficientDifferential]
    ring
  have hright :
      J = quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1) * C) +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1) * E) := by
    calc
      J = y ^ (m - 1) * Q := hQ
      _ = quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1)) *
          (quadraticBaseSubstitutionAlgHom k hk C +
            Germ.coordinate (0 : Fin 2) *
              quadraticBaseSubstitutionAlgHom k hk E) := by
        rw [hyPower, hp]
      _ = quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1) * C) +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk (y ^ (m - 1) * E) := by
        rw [map_mul, map_mul]
        ring
  obtain ⟨hcoefficient, hodd⟩ :=
    quadraticBase_decomposition_unique k hk hleft hright
  constructor
  · have htwoDvd : y ^ (m - 1) ∣
        2 * Germ.partialDerivative (1 : Fin 2) A :=
      ⟨E, hodd⟩
    have htwoUnit : IsUnit (2 : Germ 2) := by
      rw [Germ.isUnit_iff_valueRingHom_ne_zero]
      change (2 : ℂ) ≠ 0
      norm_num
    exact htwoUnit.dvd_mul_left.mp htwoDvd
  · exact ⟨C, hcoefficient⟩

end Germ

end OnLeConjecture.DTwo
