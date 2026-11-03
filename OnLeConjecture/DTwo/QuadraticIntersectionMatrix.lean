/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticRemainder

/-!
# The intersection matrix for an even quadratic curve

Multiplication by a plane germ on the quotient by `x²+yᵏ` is represented on
the quadratic remainder module by a matrix of size two. For an even exponent,
its determinant is the product of the restrictions to the two branches.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

namespace Germ

/-- Multiplication by a quadratic remainder on the free module of rank two. -/
@[expose]
noncomputable def quadraticRemainderMultiplication
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    (Fin 2 → Germ 1) →ₗ[Germ 1] (Fin 2 → Germ 1) where
  toFun v := ![
    quadraticBaseRemainder k hk u 0 * v 0 -
      Germ.coordinate (0 : Fin 1) ^ k *
        quadraticBaseRemainder k hk u 1 * v 1,
    quadraticBaseRemainder k hk u 1 * v 0 +
      quadraticBaseRemainder k hk u 0 * v 1]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp]
theorem quadraticRemainderMultiplication_apply_zero
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) (v : Fin 2 → Germ 1) :
    quadraticRemainderMultiplication k hk u v 0 =
      quadraticBaseRemainder k hk u 0 * v 0 -
        Germ.coordinate (0 : Fin 1) ^ k *
          quadraticBaseRemainder k hk u 1 * v 1 :=
  rfl

@[simp]
theorem quadraticRemainderMultiplication_apply_one
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) (v : Fin 2 → Germ 1) :
    quadraticRemainderMultiplication k hk u v 1 =
      quadraticBaseRemainder k hk u 1 * v 0 +
        quadraticBaseRemainder k hk u 0 * v 1 :=
  rfl

private theorem quadraticBaseCoefficientPair_mul
    (k : ℕ) (hk : 1 ≤ k) (u f : Germ 2) :
    quadraticBaseCoefficientPair k hk (u * f) =
      ((quadraticBaseCoefficientPair k hk u).1 *
          (quadraticBaseCoefficientPair k hk f).1 +
        (Germ.coordinate (0 : Fin 2) -
            Germ.coordinate (1 : Fin 2) ^ k) *
          (quadraticBaseCoefficientPair k hk u).2 *
          (quadraticBaseCoefficientPair k hk f).2,
      (quadraticBaseCoefficientPair k hk u).1 *
          (quadraticBaseCoefficientPair k hk f).2 +
        (quadraticBaseCoefficientPair k hk u).2 *
          (quadraticBaseCoefficientPair k hk f).1) := by
  apply quadraticBaseCoefficientPair_eq
  calc
    u * f =
        (quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk u).1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (quadraticBaseCoefficientPair k hk u).2) *
        (quadraticBaseSubstitutionAlgHom k hk
            (quadraticBaseCoefficientPair k hk f).1 +
          Germ.coordinate (0 : Fin 2) *
            quadraticBaseSubstitutionAlgHom k hk
              (quadraticBaseCoefficientPair k hk f).2) := by
      exact congrArg₂ (fun q r : Germ 2 ↦ q * r)
        (quadraticBaseCoefficientPair_spec k hk u)
        (quadraticBaseCoefficientPair_spec k hk f)
    _ = quadraticBaseSubstitutionAlgHom k hk
          ((quadraticBaseCoefficientPair k hk u).1 *
              (quadraticBaseCoefficientPair k hk f).1 +
            (Germ.coordinate (0 : Fin 2) -
                Germ.coordinate (1 : Fin 2) ^ k) *
              (quadraticBaseCoefficientPair k hk u).2 *
              (quadraticBaseCoefficientPair k hk f).2) +
        Germ.coordinate (0 : Fin 2) *
          quadraticBaseSubstitutionAlgHom k hk
            ((quadraticBaseCoefficientPair k hk u).1 *
                (quadraticBaseCoefficientPair k hk f).2 +
              (quadraticBaseCoefficientPair k hk u).2 *
                (quadraticBaseCoefficientPair k hk f).1) := by
      simp only [map_add, map_mul, map_sub, map_pow,
        quadraticBaseSubstitutionAlgHom_coordinate_zero,
        quadraticBaseSubstitutionAlgHom_coordinate_one]
      ring

/-- The remainder of a product is obtained by the multiplication matrix. -/
theorem quadraticBaseRemainder_mul
    (k : ℕ) (hk : 1 ≤ k) (u f : Germ 2) :
    quadraticBaseRemainder k hk (u * f) =
      quadraticRemainderMultiplication k hk u
        (quadraticBaseRemainder k hk f) := by
  funext i
  fin_cases i
  · change quadraticBaseRemainder k hk (u * f) 0 =
      quadraticRemainderMultiplication k hk u
        (quadraticBaseRemainder k hk f) 0
    have hcoord : Germ.hyperplaneRestriction 1
        (Germ.coordinate (1 : Fin 2)) =
        Germ.coordinate (0 : Fin 1) := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
        Germ.hyperplaneRestriction_coordinate_succ]
    rw [quadraticBaseRemainder_apply_zero,
      quadraticBaseCoefficientPair_mul]
    simp only [map_add, map_mul, map_sub, map_pow,
      Germ.hyperplaneRestriction_coordinate_zero,
      zero_sub, hcoord]
    change _ = quadraticRemainderMultiplication k hk u
      (quadraticBaseRemainder k hk f) 0
    simp [quadraticRemainderMultiplication]
    ring
  · change quadraticBaseRemainder k hk (u * f) 1 =
      quadraticRemainderMultiplication k hk u
        (quadraticBaseRemainder k hk f) 1
    rw [quadraticBaseRemainder_apply_one,
      quadraticBaseCoefficientPair_mul]
    simp only [map_add, map_mul]
    simp [quadraticRemainderMultiplication]
    ring

/-- The determinant of the quadratic multiplication matrix. -/
theorem det_quadraticRemainderMultiplication
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    LinearMap.det (quadraticRemainderMultiplication k hk u) =
      quadraticBaseRemainder k hk u 0 ^ 2 +
        Germ.coordinate (0 : Fin 1) ^ k *
          quadraticBaseRemainder k hk u 1 ^ 2 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun (Germ 1) (Fin 2)),
    Matrix.det_fin_two]
  simp [quadraticRemainderMultiplication]
  ring

/-- Restriction to an even branch is evaluation of the quadratic remainder. -/
theorem evenQuadraticBranchMapGerm_pullback_eq_remainder
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u =
      quadraticBaseRemainder (2 * a) (by omega) u 0 +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
          quadraticBaseRemainder (2 * a) (by omega) u 1 := by
  change (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u =
    Germ.hyperplaneRestriction 1
        (quadraticBaseCoefficientPair (2 * a) (by omega) u).1 +
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
        Germ.hyperplaneRestriction 1
          (quadraticBaseCoefficientPair (2 * a) (by omega) u).2
  conv_lhs =>
    rw [quadraticBaseCoefficientPair_spec (2 * a) (by omega) u]
  rw [map_add, map_mul,
    Germ.evenQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      a ha epsilon hepsilon,
    Germ.evenQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.evenQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      a ha epsilon hepsilon]

/-- For an even quadratic curve, the determinant is the product of the two
branch restrictions. -/
theorem det_quadraticRemainderMultiplication_even
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2) :
    LinearMap.det
        (quadraticRemainderMultiplication (2 * a) (by omega) u) =
      (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u *
        (Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom u := by
  have hnegative : (-epsilon) ^ 2 = -1 := by
    rw [neg_sq, hepsilon]
  rw [det_quadraticRemainderMultiplication,
    evenQuadraticBranchMapGerm_pullback_eq_remainder
      a ha epsilon hepsilon,
    evenQuadraticBranchMapGerm_pullback_eq_remainder
      a ha (-epsilon) hnegative]
  have hepsilonGerm :
      (Germ.constRingHom 1 epsilon : Germ 1) ^ 2 = -1 := by
    rw [← map_pow, hepsilon]
    simp
  simp only [map_neg]
  rw [show Germ.coordinate (0 : Fin 1) ^ (2 * a) =
      (Germ.coordinate (0 : Fin 1) ^ a) ^ 2 by
        rw [pow_two, ← pow_add]
        congr 1
        omega]
  ring_nf
  rw [hepsilonGerm]
  ring

/-- The quotient map from plane germs to the cokernel of multiplication on
the quadratic remainder module. -/
@[expose]
noncomputable def quadraticCokernelMap
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    Germ 2 →ₗ[ℂ]
      ((Fin 2 → Germ 1) ⧸
        LinearMap.range (quadraticRemainderMultiplication k hk u)) :=
  (((LinearMap.range (quadraticRemainderMultiplication k hk u)).mkQ
      ).restrictScalars ℂ).comp (quadraticBaseRemainder k hk)

/-- The map from plane germs to the multiplication cokernel is onto. -/
theorem quadraticCokernelMap_surjective
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    Function.Surjective (quadraticCokernelMap k hk u) := by
  intro q
  rcases Submodule.mkQ_surjective
      (LinearMap.range (quadraticRemainderMultiplication k hk u)) q with
    ⟨v, rfl⟩
  rcases quadraticBaseRemainder_surjective k hk v with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  simp only [quadraticCokernelMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, hf]

/-- The kernel of the cokernel map is generated by the quadratic equation and
the multiplying germ. -/
theorem ker_quadraticCokernelMap
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    LinearMap.ker (quadraticCokernelMap k hk u) =
      (pairIdeal (quadraticBaseEquation k) u).restrictScalars ℂ := by
  ext f
  constructor
  · intro hf
    rw [LinearMap.mem_ker] at hf
    simp only [quadraticCokernelMap, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply] at hf
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hf
    rcases hf with ⟨v, hv⟩
    rcases quadraticBaseRemainder_surjective k hk v with ⟨q, hq⟩
    have hrem : quadraticBaseRemainder k hk (f - u * q) = 0 := by
      rw [map_sub, quadraticBaseRemainder_mul, hq, hv]
      exact sub_self _
    have hspan : f - u * q ∈ Ideal.span {quadraticBaseEquation k} := by
      have : f - u * q ∈ LinearMap.ker (quadraticBaseRemainder k hk) := hrem
      rw [ker_quadraticBaseRemainder] at this
      exact this
    rw [Ideal.mem_span_singleton'] at hspan
    rcases hspan with ⟨c, hc⟩
    change f ∈ pairIdeal (quadraticBaseEquation k) u
    rw [pairIdeal_eq_span, Ideal.mem_span_pair]
    refine ⟨c, q, ?_⟩
    rw [hc]
    ring
  · intro hf
    change f ∈ pairIdeal (quadraticBaseEquation k) u at hf
    rw [pairIdeal_eq_span, Ideal.mem_span_pair] at hf
    rcases hf with ⟨c, q, hfactor⟩
    rw [LinearMap.mem_ker]
    simp only [quadraticCokernelMap, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [LinearMap.mem_range]
    refine ⟨quadraticBaseRemainder k hk q, ?_⟩
    have hcg : quadraticBaseRemainder k hk
        (c * quadraticBaseEquation k) = 0 := by
      have hmem : c * quadraticBaseEquation k ∈
          Ideal.span {quadraticBaseEquation k} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨c, rfl⟩
      have : c * quadraticBaseEquation k ∈
          LinearMap.ker (quadraticBaseRemainder k hk) := by
        rw [ker_quadraticBaseRemainder]
        exact hmem
      exact this
    calc
      quadraticRemainderMultiplication k hk u
          (quadraticBaseRemainder k hk q) =
          quadraticBaseRemainder k hk (u * q) :=
        (quadraticBaseRemainder_mul k hk u q).symm
      _ = quadraticBaseRemainder k hk
          (c * quadraticBaseEquation k + q * u) := by
        rw [map_add, hcg, zero_add]
        rw [mul_comm q u]
      _ = quadraticBaseRemainder k hk f := by rw [hfactor]

/-- The local algebra of the quadratic equation and a second germ is linearly
equivalent to the cokernel of its multiplication matrix. -/
@[expose]
noncomputable def quadraticPairQuotientEquivCokernel
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2) :
    (Germ 2 ⧸
        (pairIdeal (quadraticBaseEquation k) u).restrictScalars ℂ) ≃ₗ[ℂ]
      ((Fin 2 → Germ 1) ⧸
        LinearMap.range (quadraticRemainderMultiplication k hk u)) :=
  (Submodule.Quotient.equiv
      ((pairIdeal (quadraticBaseEquation k) u).restrictScalars ℂ)
      (LinearMap.ker (quadraticCokernelMap k hk u))
      (LinearEquiv.refl ℂ (Germ 2))
      (by
        rw [ker_quadraticCokernelMap]
        simp)).trans
    ((quadraticCokernelMap k hk u).quotKerEquivOfSurjective
      (quadraticCokernelMap_surjective k hk u))

/-- The intersection number with `x²+yᵏ` is the order of the determinant of
the multiplication matrix. -/
theorem intersectionMultiplicity_quadraticBaseEquation_eq_det_order
    (k : ℕ) (hk : 1 ≤ k) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation k) u)
    (hdet : LinearMap.det (quadraticRemainderMultiplication k hk u) ≠ 0) :
    intersectionMultiplicity (quadraticBaseEquation k) u hfinite =
      (Germ.vanishingOrder
        (LinearMap.det
          (quadraticRemainderMultiplication k hk u))).toNat := by
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ pairIdeal (quadraticBaseEquation k) u) := hfinite
  change Module.finrank ℂ
      (Germ 2 ⧸ pairIdeal (quadraticBaseEquation k) u) = _
  calc
    Module.finrank ℂ
        (Germ 2 ⧸ pairIdeal (quadraticBaseEquation k) u) =
        Module.finrank ℂ
          ((Fin 2 → Germ 1) ⧸
            LinearMap.range (quadraticRemainderMultiplication k hk u)) :=
      (quadraticPairQuotientEquivCokernel k hk u).finrank_eq
    _ = (Germ.vanishingOrder
          (LinearMap.det
            (quadraticRemainderMultiplication k hk u))).toNat :=
      Germ.finrank_quotient_range_eq_vanishingOrder_det_toNat _ hdet

/-- Finite intersection with the even quadratic equation makes both branch
restrictions nonzero. -/
theorem evenQuadraticBranchMapGerm_pullbacks_ne_zero_of_base
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation (2 * a)) u) :
    (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u ≠ 0 ∧
      (evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom u ≠ 0 := by
  apply evenQuadraticBranchMapGerm_pullbacks_ne_zero
    a ha epsilon hepsilon u
  simpa [quadraticBaseEquation] using hfinite

/-- The first factor of an even quadratic equation has finite intersection
with any germ that meets the equation with finite multiplicity. -/
theorem hasFiniteIntersection_evenBranchFactor_positive_of_base
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation (2 * a)) u) :
    HasFiniteIntersection (evenBranchFactor a epsilon) u :=
  hasFiniteIntersection_evenBranchFactor_of_pullback_ne_zero
    a ha epsilon u
      (evenQuadraticBranchMapGerm_pullbacks_ne_zero_of_base
        a ha epsilon hepsilon u hfinite).1

/-- The second factor of an even quadratic equation has finite intersection
with any germ that meets the equation with finite multiplicity. -/
theorem hasFiniteIntersection_evenBranchFactor_negative_of_base
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation (2 * a)) u) :
    HasFiniteIntersection (evenBranchFactor a (-epsilon)) u :=
  hasFiniteIntersection_evenBranchFactor_of_pullback_ne_zero
    a ha (-epsilon) u
      (evenQuadraticBranchMapGerm_pullbacks_ne_zero_of_base
        a ha epsilon hepsilon u hfinite).2

/-- Intersection multiplicity with an even quadratic equation is the sum of
the intersection multiplicities with its two branches. -/
theorem intersectionMultiplicity_even_quadratic_eq_branch_sum
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation (2 * a)) u) :
    intersectionMultiplicity (quadraticBaseEquation (2 * a)) u hfinite =
      intersectionMultiplicity (evenBranchFactor a epsilon) u
          (hasFiniteIntersection_evenBranchFactor_positive_of_base
            a ha epsilon hepsilon u hfinite) +
        intersectionMultiplicity (evenBranchFactor a (-epsilon)) u
          (hasFiniteIntersection_evenBranchFactor_negative_of_base
            a ha epsilon hepsilon u hfinite) := by
  let pPlus :=
    (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u
  let pMinus :=
    (evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom u
  have hne := evenQuadraticBranchMapGerm_pullbacks_ne_zero_of_base
    a ha epsilon hepsilon u hfinite
  have hplus : pPlus ≠ 0 := hne.1
  have hminus : pMinus ≠ 0 := hne.2
  have hdet : LinearMap.det
      (quadraticRemainderMultiplication (2 * a) (by omega) u) ≠ 0 := by
    rw [det_quadraticRemainderMultiplication_even
      a ha epsilon hepsilon u]
    exact mul_ne_zero hplus hminus
  have hplusOrder : Germ.vanishingOrder pPlus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hplus
  have hminusOrder : Germ.vanishingOrder pMinus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hminus
  calc
    intersectionMultiplicity (quadraticBaseEquation (2 * a)) u hfinite =
        (Germ.vanishingOrder
          (LinearMap.det
            (quadraticRemainderMultiplication
              (2 * a) (by omega) u))).toNat :=
      intersectionMultiplicity_quadraticBaseEquation_eq_det_order
        (2 * a) (by omega) u hfinite hdet
    _ = (Germ.vanishingOrder (pPlus * pMinus)).toNat := by
      rw [det_quadraticRemainderMultiplication_even
        a ha epsilon hepsilon u]
    _ = (Germ.vanishingOrder pPlus).toNat +
        (Germ.vanishingOrder pMinus).toNat := by
      rw [Germ.vanishingOrder_mul,
        ENat.toNat_add hplusOrder hminusOrder]
    _ = intersectionMultiplicity (evenBranchFactor a epsilon) u
          (hasFiniteIntersection_evenBranchFactor_positive_of_base
            a ha epsilon hepsilon u hfinite) +
        intersectionMultiplicity (evenBranchFactor a (-epsilon)) u
          (hasFiniteIntersection_evenBranchFactor_negative_of_base
            a ha epsilon hepsilon u hfinite) := by
      rw [intersectionMultiplicity_evenBranchFactor_eq_order
          a ha epsilon u hplus,
        intersectionMultiplicity_evenBranchFactor_eq_order
          a ha (-epsilon) u hminus]

/-- Intersection multiplicity is additive across the explicit factorization
of an even quadratic equation. -/
theorem intersectionMultiplicity_evenBranchFactor_mul
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection
      (evenBranchFactor a epsilon * evenBranchFactor a (-epsilon)) u) :
    intersectionMultiplicity
        (evenBranchFactor a epsilon * evenBranchFactor a (-epsilon)) u
        hfinite =
      intersectionMultiplicity (evenBranchFactor a epsilon) u
          (hasFiniteIntersection_left_of_mul
            (evenBranchFactor a epsilon) (evenBranchFactor a (-epsilon))
              u hfinite) +
        intersectionMultiplicity (evenBranchFactor a (-epsilon)) u
          (hasFiniteIntersection_right_of_mul
            (evenBranchFactor a epsilon) (evenBranchFactor a (-epsilon))
              u hfinite) := by
  have hbase : HasFiniteIntersection
      (quadraticBaseEquation (2 * a)) u := by
    rw [quadraticBaseEquation]
    rw [← evenBranchFactor_mul_negative a epsilon hepsilon]
    exact hfinite
  have hsum := intersectionMultiplicity_even_quadratic_eq_branch_sum
    a ha epsilon hepsilon u hbase
  simpa only [quadraticBaseEquation,
    ← evenBranchFactor_mul_negative a epsilon hepsilon] using hsum

end Germ

end OnLeConjecture.DTwo
