/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicAxisDecomposition
public import OnLeConjecture.DTwo.CyclicSmallExponentExclusion
public import OnLeConjecture.Analytic.TargetAxisTriangularNormalization

/-!
# Normalizing the minimum odd axis coefficient

A nonzero odd coefficient of minimum one-variable order divides the other
odd coefficient. Analytic triangular target changes then give an odd
monomial in the second component and a third component divisible by `y^k`.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_cyclic_normal_form_of_axis_decompositions
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (A B C D : Germ 1) (hA : A ∈ maximalIdeal 1) (hC : C ∈ maximalIdeal 1)
    (hB : B ≠ 0) (hBzero : valueRingHom 1 B = 0) (hBD : B ∣ D)
    (H₂ H₃ : Germ 2)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom B + coordinate 1 ^ k * H₂)
    (hZ : g.1.component 2 = (cyclicScalarMap k (by omega)).pullbackRingHom C +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom D + coordinate 1 ^ k * H₃) :
    ∃ p : ℕ, ∃ f : PointedMapGerm 2 3, ∃ h₂ h₃ : Germ 2,
      3 ≤ p ∧ Odd p ∧ g.RightLeftEquivalent f ∧
      f.1.component 0 = cyclicFirst k ∧
      f.1.component 1 = cyclicSecond k p h₂ ∧ f.1.component 2 = coordinate 1 ^ k * h₃ ∧
      (valueRingHom 2 H₂ ≠ 0 ∨ valueRingHom 2 H₃ ≠ 0 →
        valueRingHom 2 h₂ ≠ 0 ∨ valueRingHom 2 h₃ ≠ 0) := by
  obtain ⟨v, hv⟩ := hBD
  obtain ⟨r, u, hu, hBu⟩ := Germ.exists_eq_coordinate_pow_mul_unit hB
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have hBeq : B = u := by simpa [hr0] using hBu
    have hBunit : IsUnit B := hBeq ▸ hu
    exact (isUnit_iff_valueRingHom_ne_zero.mp hBunit) hBzero
  let uinv : Germ 1 := ↑(hu.unit⁻¹)
  have huinv : IsUnit uinv := (hu.unit⁻¹).isUnit
  have huuinv : u * uinv = 1 := by
    change u * ↑(hu.unit⁻¹) = 1
    calc
      u * ↑(hu.unit⁻¹) = ↑hu.unit * ↑(hu.unit⁻¹) :=
        congrArg (fun t : Germ 1 => t * ↑(hu.unit⁻¹)) hu.unit_spec.symm
      _ = 1 := Units.mul_inv hu.unit
  let σ := cyclicScalarMap k (by omega : 1 ≤ k)
  have hscalar : g.firstCoordinateTriple = σ := by
    apply PointedMapGerm.ext_components
    intro i
    rw [PointedMapGerm.firstCoordinateTriple_component, hP, cyclicScalarMap_component]
    rfl
  obtain ⟨f, hgf, hf0, hf1, hf2⟩ :=
    g.exists_target_axis_triangular_normalization A C uinv v hA hC huinv
  rw [hscalar] at hf1 hf2
  have hpow : coordinate (1 : Fin 2) ^ k ∣
      (cyclicFirst k) ^ r - (coordinate (0 : Fin 2) ^ 2) ^ r := by
    have h := sub_dvd_pow_sub_pow
      (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k)
      (coordinate (0 : Fin 2) ^ 2) r
    have heq : coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k - coordinate 0 ^ 2 =
        coordinate 1 ^ k := by ring
    rw [heq] at h
    exact h
  obtain ⟨W, hW⟩ := hpow
  let h₂ : Germ 2 := coordinate 0 * W + H₂ * σ.pullbackRingHom uinv
  let h₃ : Germ 2 := H₃ - H₂ * σ.pullbackRingHom v
  refine ⟨2 * r + 1, f, h₂, h₃, by omega, ⟨r, by omega⟩,
    hgf, hf0.trans hP, ?_, ?_, ?_⟩
  · have hBpull : σ.pullbackRingHom B * σ.pullbackRingHom uinv = (cyclicFirst k) ^ r := by
      rw [hBu, map_mul, map_pow, PointedMapGerm.pullback_coordinate,
        cyclicScalarMap_component, mul_assoc, ← map_mul, huuinv, map_one, mul_one]
      rfl
    rw [hf1, hQ]
    change (((σ.pullbackRingHom A + coordinate 0 * σ.pullbackRingHom B) +
      coordinate 1 ^ k * H₂) - σ.pullbackRingHom A) * σ.pullbackRingHom uinv = _
    have hnormal : (cyclicFirst k) ^ r =
        (coordinate (0 : Fin 2) ^ 2) ^ r + coordinate 1 ^ k * W := by
      linear_combination hW
    calc
      _ = coordinate 0 * (σ.pullbackRingHom B * σ.pullbackRingHom uinv) +
          coordinate 1 ^ k * (H₂ * σ.pullbackRingHom uinv) := by ring
      _ = cyclicSecond k (2 * r + 1) h₂ := by
        rw [hBpull, hnormal]
        simp only [cyclicSecond, h₂, pow_mul, pow_add, pow_one]
        ring
  · rw [hf2, hZ, hQ, hv, map_mul]
    change ((σ.pullbackRingHom C + coordinate 0 *
        (σ.pullbackRingHom B * σ.pullbackRingHom v) + coordinate 1 ^ k * H₃) -
      σ.pullbackRingHom C) -
      ((σ.pullbackRingHom A + coordinate 0 * σ.pullbackRingHom B + coordinate 1 ^ k * H₂) -
        σ.pullbackRingHom A) * σ.pullbackRingHom v = _
    dsimp only [h₃]
    ring
  · intro hunit
    have hvalue₂ : valueRingHom 2 h₂ = valueRingHom 2 H₂ * valueRingHom 1 uinv := by
      simp only [h₂, map_add, map_mul, valueRingHom_coordinate, zero_mul,
        zero_add, PointedMapGerm.valueRingHom_pullback]
    have hvalue₃ : valueRingHom 2 h₃ = valueRingHom 2 H₃ -
        valueRingHom 2 H₂ * valueRingHom 1 v := by
      simp only [h₃, map_sub, map_mul, PointedMapGerm.valueRingHom_pullback]
    by_cases h₂zero : valueRingHom 2 H₂ = 0
    · right
      rw [hvalue₃, h₂zero, zero_mul, sub_zero]
      exact hunit.resolve_left (not_not.mpr h₂zero)
    · left
      rw [hvalue₂]
      exact mul_ne_zero h₂zero (isUnit_iff_valueRingHom_ne_zero.mp huinv)

/-- With a unit transverse coefficient the constructed normal form is
excluded by the complete analytic cyclic collision theorem. -/
theorem not_hasInjectiveRepresentative_of_axis_decompositions
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (A B C D : Germ 1) (hA : A ∈ maximalIdeal 1) (hC : C ∈ maximalIdeal 1)
    (hB : B ≠ 0) (hBzero : valueRingHom 1 B = 0) (hBD : B ∣ D)
    (H₂ H₃ : Germ 2) (hunit : valueRingHom 2 H₂ ≠ 0 ∨ valueRingHom 2 H₃ ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom B + coordinate 1 ^ k * H₂)
    (hZ : g.1.component 2 = (cyclicScalarMap k (by omega)).pullbackRingHom C +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom D + coordinate 1 ^ k * H₃) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨p, f, h₂, h₃, hp, hodd, hgf, hf0, hf1, hf2, hunits⟩ :=
    exists_cyclic_normal_form_of_axis_decompositions g k hk A B C D hA hC
      hB hBzero hBD H₂ H₃ hP hQ hZ
  intro hg
  exact cyclic_normal_form_not_hasInjectiveRepresentative_of_two_le f k p hk hp hodd
    h₂ h₃ (hunits hunit) hf0 hf1 hf2 (hgf.hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
