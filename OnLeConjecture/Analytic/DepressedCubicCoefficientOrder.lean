/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrderThreeMapNormalization

/-!
# Coefficient orders in a depressed cubic

Membership of a depressed monic cubic in the cube of the plane maximal ideal
is equivalent to the expected orders of its two coefficient germs. An
analytic unit factor does not change this condition.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Pullback by a pointed analytic map germ carries every power of the target
maximal ideal into the corresponding power of the source maximal ideal. -/
theorem pullback_mem_maximalIdeal_pow {n m N : ℕ}
    (f : PointedMapGerm n m) {q : Germ m}
    (hq : q ∈ Germ.maximalIdeal m ^ N) :
    f.pullbackRingHom q ∈ Germ.maximalIdeal n ^ N := by
  have hmaximal :
      Ideal.map f.pullbackRingHom (Germ.maximalIdeal m) ≤
        Germ.maximalIdeal n := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact f.pullback_mem_maximalIdeal hr
  have hmap :
      Ideal.map f.pullbackRingHom (Germ.maximalIdeal m ^ N) ≤
        Germ.maximalIdeal n ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmaximal N
  exact hmap (Ideal.mem_map_of_mem f.pullbackRingHom hq)

end PointedMapGerm

namespace Germ

/-- Restriction to the first coordinate hyperplane is a left inverse to
extension from that hyperplane. -/
@[simp]
theorem hyperplaneRestriction_hyperplaneExtension {n : ℕ} (q : Germ n) :
    Germ.hyperplaneRestriction n (Germ.hyperplaneExtension n q) = q := by
  exact DFunLike.congr_fun (Germ.hyperplaneRestriction_comp_extension n) q

/-- A partial derivative carries the next power of the analytic maximal ideal
into the given power. -/
theorem partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ
    {n k : ℕ} (i : Fin n) {f : Germ n}
    (hf : f ∈ Germ.maximalIdeal n ^ (k + 1)) :
    Germ.partialDerivative i f ∈ Germ.maximalIdeal n ^ k := by
  let I := Germ.maximalIdeal n
  induction k generalizing f with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ k ih =>
      have hf' : f ∈ I ^ (k + 1) * I := by
        simpa only [show (k + 1 + 1 : ℕ) = (k + 1) + 1 by omega,
          Submodule.pow_succ] using hf
      refine Submodule.mul_induction_on hf' ?_ ?_
      · intro a ha b hb
        rw [Germ.partialDerivative_mul]
        apply (I ^ (k + 1)).add_mem
        · have hda : Germ.partialDerivative i a ∈ I ^ k := ih ha
          have hproduct := Ideal.mul_mem_mul hda hb
          simpa only [Submodule.pow_succ] using hproduct
        · exact Ideal.mul_mem_right (Germ.partialDerivative i b)
            (I ^ (k + 1)) ha
      · intro a b ha hb
        rw [Germ.partialDerivative_add]
        exact (I ^ (k + 1)).add_mem ha hb

/-- Membership of a depressed cubic in the cube of the plane maximal ideal
forces the linear and constant coefficient germs to have orders at least two
and three. -/
theorem depressedCubic_coefficients_mem_maximalIdeal_powers
    (a₁ a₀ : Germ 1)
    (hmem :
      Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀ ∈
        Germ.maximalIdeal 2 ^ 3) :
    a₁ ∈ Germ.maximalIdeal 1 ^ 2 ∧
      a₀ ∈ Germ.maximalIdeal 1 ^ 3 := by
  let P : Germ 2 :=
    Germ.coordinate (0 : Fin 2) ^ 3 +
      Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
      Germ.planeCoefficientExtension a₀
  change P ∈ Germ.maximalIdeal 2 ^ 3 at hmem
  have hderivative :
      Germ.partialDerivative (0 : Fin 2) P ∈
        Germ.maximalIdeal 2 ^ 2 := by
    exact Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ
      0 hmem
  have ha₁ :=
    PointedMapGerm.pullback_mem_maximalIdeal_pow
      (Germ.hyperplaneInclusionGerm 1) hderivative
  have ha₀ :=
    PointedMapGerm.pullback_mem_maximalIdeal_pow
      (Germ.hyperplaneInclusionGerm 1) hmem
  change Germ.hyperplaneRestriction 1
      (Germ.partialDerivative (0 : Fin 2) P) ∈
        Germ.maximalIdeal 1 ^ 2 at ha₁
  change Germ.hyperplaneRestriction 1 P ∈
      Germ.maximalIdeal 1 ^ 3 at ha₀
  have hrestrictDerivative :
      Germ.hyperplaneRestriction 1
        (Germ.partialDerivative (0 : Fin 2) P) = a₁ := by
    simp [P, Germ.planeCoefficientExtension_apply,
      Germ.partialDerivative_add, Germ.partialDerivative_mul,
      Germ.partialDerivative_pow]
  have hrestrict : Germ.hyperplaneRestriction 1 P = a₀ := by
    simp [P, Germ.planeCoefficientExtension_apply]
  rw [hrestrictDerivative] at ha₁
  rw [hrestrict] at ha₀
  exact ⟨ha₁, ha₀⟩

/-- The expected orders of the two coefficient germs place the depressed
cubic in the cube of the plane maximal ideal. -/
theorem depressedCubic_mem_maximalIdeal_cube_of_coefficients
    (a₁ a₀ : Germ 1)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ 2)
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ 3) :
    Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀ ∈
      Germ.maximalIdeal 2 ^ 3 := by
  have hx : Germ.coordinate (0 : Fin 2) ∈ Germ.maximalIdeal 2 :=
    Germ.coordinate_mem_maximalIdeal 0
  have hxCube : Germ.coordinate (0 : Fin 2) ^ 3 ∈
      Germ.maximalIdeal 2 ^ 3 :=
    Ideal.pow_mem_pow hx 3
  have ha₁Extension : Germ.planeCoefficientExtension a₁ ∈
      Germ.maximalIdeal 2 ^ 2 := by
    change (Germ.hyperplaneTailGerm 1).pullbackRingHom a₁ ∈
      Germ.maximalIdeal 2 ^ 2
    exact PointedMapGerm.pullback_mem_maximalIdeal_pow
      (Germ.hyperplaneTailGerm 1) ha₁
  have ha₀Extension : Germ.planeCoefficientExtension a₀ ∈
      Germ.maximalIdeal 2 ^ 3 := by
    change (Germ.hyperplaneTailGerm 1).pullbackRingHom a₀ ∈
      Germ.maximalIdeal 2 ^ 3
    exact PointedMapGerm.pullback_mem_maximalIdeal_pow
      (Germ.hyperplaneTailGerm 1) ha₀
  have hlinear :
      Germ.planeCoefficientExtension a₁ *
          Germ.coordinate (0 : Fin 2) ∈
        Germ.maximalIdeal 2 ^ 3 := by
    have hproduct := Ideal.mul_mem_mul ha₁Extension hx
    simpa only [show (3 : ℕ) = 2 + 1 by omega,
      Submodule.pow_succ] using hproduct
  exact (Germ.maximalIdeal 2 ^ 3).add_mem
    ((Germ.maximalIdeal 2 ^ 3).add_mem hxCube hlinear) ha₀Extension

/-- A depressed monic cubic belongs to the cube of the plane maximal ideal
exactly when its linear and constant coefficients have orders at least two
and three. -/
theorem depressedCubic_mem_maximalIdeal_cube_iff (a₁ a₀ : Germ 1) :
    Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀ ∈
        Germ.maximalIdeal 2 ^ 3 ↔
      a₁ ∈ Germ.maximalIdeal 1 ^ 2 ∧
        a₀ ∈ Germ.maximalIdeal 1 ^ 3 := by
  constructor
  · exact Germ.depressedCubic_coefficients_mem_maximalIdeal_powers a₁ a₀
  · rintro ⟨ha₁, ha₀⟩
    exact Germ.depressedCubic_mem_maximalIdeal_cube_of_coefficients
      a₁ a₀ ha₁ ha₀

/-- Multiplication by an analytic unit preserves the exact coefficient order
criterion for a depressed cubic. -/
theorem depressedCubic_mul_unit_mem_maximalIdeal_cube_iff
    (a₁ a₀ : Germ 1) (u : Germ 2) (hu : IsUnit u) :
    (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u ∈
        Germ.maximalIdeal 2 ^ 3 ↔
      a₁ ∈ Germ.maximalIdeal 1 ^ 2 ∧
        a₀ ∈ Germ.maximalIdeal 1 ^ 3 := by
  let P : Germ 2 :=
    Germ.coordinate (0 : Fin 2) ^ 3 +
      Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
      Germ.planeCoefficientExtension a₀
  change P * u ∈ Germ.maximalIdeal 2 ^ 3 ↔ _
  rw [mul_comm, (Germ.maximalIdeal 2 ^ 3).unit_mul_mem_iff_mem hu]
  exact Germ.depressedCubic_mem_maximalIdeal_cube_iff a₁ a₀

/-- The unit factored form used by the cubic normalization has the required
coefficient orders whenever the product belongs to the cube of the plane
maximal ideal. -/
theorem depressedCubic_coefficients_mem_maximalIdeal_powers_of_mul_unit
    (a₁ a₀ : Germ 1) (u : Germ 2) (hu : IsUnit u)
    (hmem :
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u ∈
        Germ.maximalIdeal 2 ^ 3) :
    a₁ ∈ Germ.maximalIdeal 1 ^ 2 ∧
      a₀ ∈ Germ.maximalIdeal 1 ^ 3 :=
  (Germ.depressedCubic_mul_unit_mem_maximalIdeal_cube_iff
    a₁ a₀ u hu).mp hmem

end Germ

namespace PointedMapGerm

/-- An injective counterexample of coordinate order three admits a depressed
cubic normalization whose two coefficient germs have orders at least two and
three. -/
theorem exists_injective_firstComponent_depressedCubic_with_coefficientOrders
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (hinjective : g.HasInjectiveRepresentative)
    (hdifferential : g.differential = 0)
    (horder : g.coordinateOrder (by omega) hfinite = 3) :
    ∃ h : PointedMapGerm 2 (n + 1), ∃ a₁ a₀ : Germ 1, ∃ u : Germ 2,
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        h.HasInjectiveRepresentative ∧ h.differential = 0 ∧
        a₁ ∈ Germ.maximalIdeal 1 ^ 2 ∧
        a₀ ∈ Germ.maximalIdeal 1 ^ 3 ∧
        IsUnit u ∧
        h.1.component 0 =
          (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.planeCoefficientExtension a₁ *
              Germ.coordinate (0 : Fin 2) +
            Germ.planeCoefficientExtension a₀) * u := by
  obtain ⟨h, a₁, a₀, u, hequivalent, hhfinite, hinjectiveH,
      hdifferentialH, _ha₁, _ha₀, hu, hcomponent⟩ :=
    g.exists_injective_firstComponent_depressedCubic
      hfinite hinjective hdifferential horder
  have horderEquality :=
    hequivalent.coordinateOrder_eq (by omega) hfinite hhfinite
  have horderH : h.coordinateOrder (by omega) hhfinite = 3 := by
    rw [← horder, ← horderEquality]
  have hcomponentMem : h.1.component 0 ∈ Germ.maximalIdeal 2 ^ 3 := by
    have hmem :=
      h.component_mem_maximalIdeal_pow_coordinateOrder
        (by omega) hhfinite 0
    simpa only [horderH] using hmem
  rw [hcomponent] at hcomponentMem
  obtain ⟨ha₁, ha₀⟩ :=
    Germ.depressedCubic_coefficients_mem_maximalIdeal_powers_of_mul_unit
      a₁ a₀ u hu hcomponentMem
  exact ⟨h, a₁, a₀, u, hequivalent, hhfinite, hinjectiveH,
    hdifferentialH, ha₁, ha₀, hu, hcomponent⟩

end PointedMapGerm

end OnLeConjecture.Analytic
