/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicCoverDescent
public import OnLeConjecture.Analytic.OneVariablePowerSubstitution

/-!
# Convergent cyclic averages in one variable

Analytic finite division, followed by restriction to a coordinate line,
expresses a germ as a finite sum of residues modulo a positive exponent.
Averaging rotations selects its residue of index zero. In particular the
descended average is an analytic germ, not just a formal power series.
-/

public section

open Filter
open scoped BigOperators

namespace OnLeConjecture.Analytic.Germ

private theorem powerPair_comp_hyperplane (k : ℕ) (hk : 0 < k) :
    (CyclicCover.powerPairGerm k hk).comp (hyperplaneInclusionGerm 1) =
      (hyperplaneInclusionGerm 1).comp (oneVariablePowerMapGerm k hk) := by
  simp only [CyclicCover.powerPairGerm, hyperplaneInclusionGerm,
    oneVariablePowerMapGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  fin_cases i
  · simp [CyclicCover.powerPairFunction, zero_pow hk.ne']
  · change z 0 ^ k = z 0 ^ k
    rfl

/-- Analytic residue decomposition under a positive power substitution. -/
theorem exists_oneVariable_power_residue_decomposition
    (k : ℕ) (hk : 0 < k) (f : Germ 1) :
    ∃ a : Fin k → Germ 1,
      f = ∑ i, (oneVariablePowerMapGerm k hk).pullbackRingHom (a i) *
        coordinate (0 : Fin 1) ^ i.1 := by
  classical
  obtain ⟨a, ha⟩ := CyclicCover.exists_power_residue_decomposition k hk
    (hyperplaneExtension 1 f)
  have hp (q : Germ 2) :
      hyperplaneRestriction 1 ((CyclicCover.powerPairGerm k hk).pullbackRingHom q) =
        (oneVariablePowerMapGerm k hk).pullbackRingHom (hyperplaneRestriction 1 q) := by
    change ((hyperplaneInclusionGerm 1).pullbackRingHom.comp
      (CyclicCover.powerPairGerm k hk).pullbackRingHom) q =
        ((oneVariablePowerMapGerm k hk).pullbackRingHom.comp
          (hyperplaneInclusionGerm 1).pullbackRingHom) q
    rw [← PointedMapGerm.pullbackRingHom_comp,
      ← PointedMapGerm.pullbackRingHom_comp, powerPair_comp_hyperplane]
  let z : Fin k := ⟨0, hk⟩
  refine ⟨fun i => hyperplaneRestriction 1 (a (z, i)), ?_⟩
  have h := congrArg (hyperplaneRestriction 1) ha
  have hleft : hyperplaneRestriction 1 (hyperplaneExtension 1 f) = f :=
    DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) f
  rw [hleft, map_sum, Fintype.sum_prod_type] at h
  simp only [map_mul, map_pow, hp, hyperplaneRestriction_coordinate_zero,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    hyperplaneRestriction_coordinate_succ] at h
  rw [h]
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro i _hi hiz
    have hi : i.1 ≠ 0 := fun hzero => hiz (Fin.ext hzero)
    simp [zero_pow hi]
  · simp

/-- Rotation by an arbitrary complex scalar. -/
@[expose] noncomputable def oneVariableRotationGerm (ζ : ℂ) : PointedMapGerm 1 1 :=
  PointedMapGerm.ofFunction (fun z => fun _ => ζ * z 0)
    (by
      apply AnalyticAt.pi
      intro i
      exact analyticAt_const.mul
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0))
    (by funext i; simp)

@[simp] theorem oneVariableRotationGerm_pullback_coordinate (ζ : ℂ) :
    (oneVariableRotationGerm ζ).pullbackRingHom (coordinate (0 : Fin 1)) =
      constRingHom 1 ζ * coordinate (0 : Fin 1) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [oneVariableRotationGerm, PointedMapGerm.ofFunction,
    MapGerm.component_ofFunction]
  rfl

theorem oneVariablePower_comp_rotation (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : ζ ^ k = 1) :
    (oneVariablePowerMapGerm k hk).comp (oneVariableRotationGerm ζ) =
      oneVariablePowerMapGerm k hk := by
  simp only [oneVariablePowerMapGerm, oneVariableRotationGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    funext i
    simp [oneVariablePowerMap, mul_pow, hζ]

theorem oneVariableRotation_power_pullback (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (a : Germ 1) :
    (oneVariableRotationGerm ζ).pullbackRingHom
        ((oneVariablePowerMapGerm k hk).pullbackRingHom a) =
      (oneVariablePowerMapGerm k hk).pullbackRingHom a := by
  change ((oneVariableRotationGerm ζ).pullbackRingHom.comp
    (oneVariablePowerMapGerm k hk).pullbackRingHom) a = _
  rw [← PointedMapGerm.pullbackRingHom_comp, oneVariablePower_comp_rotation k hk ζ hζ]

/-- The finite average of analytic rotations is analytic. -/
@[expose] noncomputable def oneVariableCyclicAverage (k : ℕ) (ζ : ℂ)
    (f : Germ 1) : Germ 1 :=
  constRingHom 1 (k : ℂ)⁻¹ *
    ∑ l ∈ Finset.range k, (oneVariableRotationGerm (ζ ^ l)).pullbackRingHom f

theorem value_oneVariableCyclicAverage (k : ℕ) (hk : 0 < k) (ζ : ℂ) (f : Germ 1) :
    valueRingHom 1 (oneVariableCyclicAverage k ζ f) = valueRingHom 1 f := by
  simp only [oneVariableCyclicAverage, map_mul, map_sum, valueRingHom_const,
    PointedMapGerm.valueRingHom_pullback, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hkC, one_mul]

/-- The cyclic average descends to a convergent germ in the powered variable. -/
theorem exists_oneVariable_cyclicAverage_descent
    (k : ℕ) (hk : 0 < k) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (f : Germ 1) :
    ∃ a : Germ 1, (oneVariablePowerMapGerm k hk).pullbackRingHom a =
      oneVariableCyclicAverage k ζ f := by
  classical
  obtain ⟨a, ha⟩ := exists_oneVariable_power_residue_decomposition k hk f
  let z : Fin k := ⟨0, hk⟩
  have hchar (i : Fin k) :
      ∑ l ∈ Finset.range k, (ζ ^ l) ^ i.1 =
        if i = z then (k : ℂ) else 0 := by
    simpa only [z, pow_zero, div_one, ← pow_mul, Nat.mul_comm] using
      CyclicCover.character_sum k hk ζ hζ i z
  have hrot (l : ℕ) (i : Fin k) :
      (oneVariableRotationGerm (ζ ^ l)).pullbackRingHom
        ((oneVariablePowerMapGerm k hk).pullbackRingHom (a i) *
          coordinate (0 : Fin 1) ^ i.1) =
      constRingHom 1 ((ζ ^ l) ^ i.1) *
        ((oneVariablePowerMapGerm k hk).pullbackRingHom (a i) *
          coordinate (0 : Fin 1) ^ i.1) := by
    rw [map_mul, map_pow, oneVariableRotation_power_pullback k hk (ζ ^ l)
      (by rw [← pow_mul, Nat.mul_comm l k, pow_mul, hζ.pow_eq_one, one_pow]),
      oneVariableRotationGerm_pullback_coordinate, mul_pow, ← map_pow]
    ring
  refine ⟨a z, ?_⟩
  unfold oneVariableCyclicAverage
  rw [ha]
  simp only [map_sum]
  simp_rw [hrot]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, hchar]
  simp only [apply_ite, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Finset.mem_univ, if_true, z, pow_zero, mul_one]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hkC, map_one, one_mul]

end OnLeConjecture.Analytic.Germ
