/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicNormalizationSubstitution
public import OnLeConjecture.Analytic.OneVariableOrder

/-!
# Convergent normalization of the second cyclic coordinate

The scalar substitution parameter is treated as an additional analytic
variable. Its parameter-zero restriction becomes a node after an
explicit analytic affine change. The proved nodal-level graph theorem
then supplies the required convergent substitution.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.DTwo.CyclicNormalization

open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ
open OnLeConjecture.Analytic.PointedMapGerm
open OnLeConjecture.Analytic.QuadraticCrossing

private noncomputable def scalarMap {n : ℕ} (f : Germ n) (hf : f ∈ maximalIdeal n) :
    PointedMapGerm n 1 :=
  (exists_with_components (fun _ : Fin 1 => f) (fun _ => hf)).choose

private theorem scalarMap_component {n : ℕ} (f : Germ n) (hf : f ∈ maximalIdeal n)
    (i : Fin 1) : (scalarMap f hf).1.component i = f :=
  (exists_with_components (fun _ : Fin 1 => f) (fun _ => hf)).choose_spec i

private noncomputable def axisMap : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (fun z => ![z 0, 0])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
      · exact analyticAt_const)
    (by ext i; fin_cases i <;> rfl)

private theorem axisMap_component (i : Fin 2) :
    axisMap.1.component i = ![coordinate 0, 0] i := by
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem scalar_special_algebra {R : Type*} [CommRing R]
    (p : ℕ) (hp : 3 ≤ p) (x z T a a₁ b c : R)
    (ha : a = c + x * a₁) (hb : b = p * x ^ (p - 2) - 2 * a)
    (hT : T * b = z - a₁) :
    T * (p * x ^ (p - 1)) + (1 - 2 * x * T) * a - c = x * z := by
  have hpow : x ^ (p - 1) = x * x ^ (p - 2) := by
    rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  rw [hb] at hT
  linear_combination ha + x * hT

/-- The analytic parameters for the normalization are constructed from
the original unit germ, not assumed as a convergent solution. -/
theorem exists_normalization_parameters (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p)
    (h : Germ 2) (hc : valueRingHom 2 h ≠ 0) :
    ∃ T v : Germ 2, ∃ b : Germ 1, ∃ f : PointedMapGerm 2 2,
      IsUnit v ∧ valueRingHom 1 b = valueRingHom 2 h ∧
      v ^ k = 1 - 2 * coordinate 0 * T - coordinate 1 ^ k * T ^ 2 ∧
      f.1.component 0 = coordinate 0 + coordinate 1 ^ k * T ∧
      f.1.component 1 = coordinate 1 * v ∧
      f.pullbackRingHom (coordinate 0 ^ p + coordinate 1 ^ k * h) =
        coordinate 0 ^ p + coordinate 1 ^ k * hyperplaneExtension 1 b := by
  let c := valueRingHom 2 h
  let a := axisMap.pullbackRingHom h
  have havalue : valueRingHom 1 a = c := axisMap.valueRingHom_pullback h
  have haMax : a - constRingHom 1 c ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, map_sub, havalue, valueRingHom_const, sub_self]
  rw [maximalIdeal_one_eq_span_coordinate, Ideal.mem_span_singleton] at haMax
  obtain ⟨a₁, ha₁⟩ := haMax
  have ha : a = constRingHom 1 c + coordinate 0 * a₁ := by
    linear_combination ha₁
  let B : Germ 1 := (p : Germ 1) * coordinate 0 ^ (p - 2) - 2 * a
  have hBvalue : valueRingHom 1 B = -2 * c := by
    dsimp only [B]
    simp [havalue, zero_pow (by omega : p - 2 ≠ 0), map_ofNat]
  have hBunit : IsUnit B := isUnit_of_valueRingHom_ne_zero (by
    rw [hBvalue]
    exact mul_ne_zero (by norm_num) hc)
  obtain ⟨bunit, hbunit⟩ := hBunit
  let BInv : Germ 1 := ↑bunit⁻¹
  have hBInv : BInv * B = 1 := by rw [← hbunit]; exact Units.inv_mul bunit
  let x : Germ 3 := coordinate 0 + coordinate 2
  let z : Germ 3 := coordinate 0 - coordinate 2
  have hxMax : x ∈ maximalIdeal 3 :=
    (maximalIdeal 3).add_mem (coordinate_mem_maximalIdeal 0) (coordinate_mem_maximalIdeal 2)
  let φ := scalarMap x hxMax
  have hφ : φ.pullbackRingHom (coordinate 0) = x := by
    rw [pullback_coordinate]
    exact scalarMap_component x hxMax 0
  let T : Germ 3 := (z - φ.pullbackRingHom a₁) * φ.pullbackRingHom BInv
  let u : Germ 3 := 1 - 2 * x * T - coordinate 1 ^ k * T ^ 2
  have huvalue : valueRingHom 3 u = 1 := by
    dsimp only [u, x]
    simp [zero_pow hk.ne']
  have huunit : IsUnit u := isUnit_of_valueRingHom_ne_zero (by rw [huvalue]; exact one_ne_zero)
  obtain ⟨v, hvunit, hvpow⟩ := exists_isUnit_pow_eq u huunit hk.ne'
  obtain ⟨r, hr⟩ := exists_with_components
    (![x + coordinate 1 ^ k * T, coordinate 1 * v] : Fin 2 → Germ 3)
    (by
      intro i
      fin_cases i
      · apply (maximalIdeal 3).add_mem hxMax
        exact (maximalIdeal 3).mul_mem_right T
          (Ideal.pow_mem_of_mem (maximalIdeal 3) (coordinate_mem_maximalIdeal 1) k hk)
      · exact (maximalIdeal 3).mul_mem_right v (coordinate_mem_maximalIdeal 1))
  have hr0 : r.1.component 0 = x + coordinate 1 ^ k * T := hr 0
  have hr1 : r.1.component 1 = coordinate 1 * v := hr 1
  let F : Germ 3 := powerQuotient p k x (coordinate 1) T +
    u * r.pullbackRingHom h - constRingHom 3 c
  have hspecial : specialGerm.pullbackRingHom F =
      coordinate (0 : Fin 2) ^ 2 - coordinate 1 ^ 2 := by
    let τ := specialGerm.pullbackRingHom T
    let χ := φ.comp specialGerm
    let X : Germ 2 := coordinate 0 + coordinate 1
    let Z : Germ 2 := coordinate 0 - coordinate 1
    have hsx : specialGerm.pullbackRingHom x = X := by
      dsimp only [x, X]
      rw [map_add, specialGerm_pullback_coordinate, specialGerm_pullback_coordinate]
      rfl
    have hsz : specialGerm.pullbackRingHom z = Z := by
      dsimp only [z, Z]
      rw [map_sub, specialGerm_pullback_coordinate, specialGerm_pullback_coordinate]
      rfl
    have hsy : specialGerm.pullbackRingHom (coordinate 1) = 0 :=
      specialGerm_pullback_coordinate 1
    have hχ : χ.pullbackRingHom (coordinate 0) = X := by
      rw [pullbackRingHom_comp]
      change specialGerm.pullbackRingHom (φ.pullbackRingHom (coordinate 0)) = _
      rw [hφ, hsx]
    have hrAxis : r.comp specialGerm = axisMap.comp χ := by
      apply ext_components
      intro i
      fin_cases i
      · change (r.comp specialGerm).1.component 0 = (axisMap.comp χ).1.component 0
        rw [component_comp_eq_pullback, component_comp_eq_pullback, hr0, axisMap_component]
        change specialGerm.pullbackRingHom (x + coordinate 1 ^ k * T) =
          χ.pullbackRingHom (coordinate 0)
        rw [map_add, map_mul, map_pow, hsx, hsy, hχ, zero_pow hk.ne', zero_mul, add_zero]
      · change (r.comp specialGerm).1.component 1 = (axisMap.comp χ).1.component 1
        rw [component_comp_eq_pullback, component_comp_eq_pullback, hr1, axisMap_component]
        change specialGerm.pullbackRingHom (coordinate 1 * v) = χ.pullbackRingHom 0
        rw [map_mul, hsy, zero_mul, map_zero]
    have hra : specialGerm.pullbackRingHom (r.pullbackRingHom h) = χ.pullbackRingHom a := by
      change (specialGerm.pullbackRingHom.comp r.pullbackRingHom) h = _
      rw [← pullbackRingHom_comp, hrAxis, pullbackRingHom_comp]
      rfl
    have hτ : τ * χ.pullbackRingHom B = Z - χ.pullbackRingHom a₁ := by
      have hT : T * φ.pullbackRingHom B = z - φ.pullbackRingHom a₁ := by
        dsimp only [T]
        rw [mul_assoc, ← map_mul, hBInv, map_one, mul_one]
      have ht := congrArg specialGerm.pullbackRingHom hT
      simpa only [map_mul, map_sub, hsz, χ, pullbackRingHom_comp, RingHom.comp_apply] using ht
    have haχ : χ.pullbackRingHom a = constRingHom 2 c + X * χ.pullbackRingHom a₁ := by
      rw [ha, map_add, pullback_constRingHom, map_mul, hχ]
    have hbχ : χ.pullbackRingHom B = p * X ^ (p - 2) - 2 * χ.pullbackRingHom a := by
      dsimp only [B]
      rw [map_sub, map_mul, map_mul, map_pow, map_natCast, map_ofNat, hχ]
    have hF : specialGerm.pullbackRingHom F =
        τ * (p * X ^ (p - 1)) + (1 - 2 * X * τ) * χ.pullbackRingHom a -
          constRingHom 2 c := by
      have hsu : specialGerm.pullbackRingHom u = 1 - 2 * X * τ := by
        calc
          specialGerm.pullbackRingHom u =
              1 - 2 * specialGerm.pullbackRingHom x * τ -
                specialGerm.pullbackRingHom (coordinate 1) ^ k * τ ^ 2 := by
            simp only [u, map_sub, map_mul, map_pow, map_one, map_ofNat]
            rfl
          _ = _ := by rw [hsx, hsy, zero_pow hk.ne', zero_mul, sub_zero]
      dsimp only [F]
      rw [map_sub, map_add, map_mul, map_powerQuotient, hsx, hsy,
        powerQuotient_zero p k hk, pullback_constRingHom, hra, hsu]
    rw [hF, scalar_special_algebra p hp X Z τ (χ.pullbackRingHom a)
      (χ.pullbackRingHom a₁) (χ.pullbackRingHom B) (constRingHom 2 c) haχ hbχ hτ]
    dsimp only [X, Z]
    ring
  obtain ⟨b, s, hb, hsx, hsy, hsF⟩ :=
    ParametricNodalLevel.exists_level_graph_of_special F hspecial
  let T' := s.pullbackRingHom T
  let v' := s.pullbackRingHom v
  let f := r.comp s
  let β := constRingHom 1 c + b
  have hsX : s.pullbackRingHom x = coordinate 0 := by
    dsimp only [x]
    rw [map_add, pullback_coordinate, pullback_coordinate, hsx]
  have hsY : s.pullbackRingHom (coordinate 1) = coordinate 1 := by
    rw [pullback_coordinate, hsy]
  have hf0 : f.1.component 0 = coordinate 0 + coordinate 1 ^ k * T' := by
    rw [component_comp_eq_pullback, hr0, map_add, map_mul, map_pow, hsX, hsY]
  have hf1 : f.1.component 1 = coordinate 1 * v' := by
    rw [component_comp_eq_pullback, hr1, map_mul, hsY]
  have hvroot : v' ^ k = 1 - 2 * coordinate 0 * T' - coordinate 1 ^ k * T' ^ 2 := by
    change s.pullbackRingHom v ^ k = _
    rw [← map_pow, hvpow]
    calc
      s.pullbackRingHom u = 1 - 2 * s.pullbackRingHom x * T' -
          s.pullbackRingHom (coordinate 1) ^ k * T' ^ 2 := by
        simp only [u, map_sub, map_mul, map_pow, map_one, map_ofNat]
        rfl
      _ = _ := by rw [hsX, hsY]
  refine ⟨T', v', β, f, hvunit.map s.pullbackRingHom, ?_, hvroot, hf0, hf1, ?_⟩
  · dsimp only [β]
    rw [map_add, valueRingHom_const, mem_maximalIdeal_iff.mp hb, add_zero]
  · have hsum : powerQuotient p k (coordinate 0) (coordinate 1) T' +
        v' ^ k * f.pullbackRingHom h = hyperplaneExtension 1 β := by
      dsimp only [F] at hsF
      rw [map_sub, map_add, map_mul, map_powerQuotient, hsX, hsY,
        pullback_constRingHom] at hsF
      have hunit : s.pullbackRingHom u = v' ^ k := by rw [← hvpow, map_pow]
      rw [hunit] at hsF
      have hfh : f.pullbackRingHom h = s.pullbackRingHom (r.pullbackRingHom h) := by
        rw [pullbackRingHom_comp]
        rfl
      rw [← hfh] at hsF
      dsimp only [β]
      rw [map_add]
      have hconst : hyperplaneExtension 1 (constRingHom 1 c) = constRingHom 2 c :=
        (hyperplaneTailGerm 1).pullback_constRingHom c
      rw [hconst]
      linear_combination hsF
    rw [map_add, map_pow, map_mul, map_pow, pullback_coordinate, pullback_coordinate,
      hf0, hf1, powerQuotient_identity, mul_pow]
    linear_combination coordinate (1 : Fin 2) ^ k * hsum

/-- An arbitrary analytic unit coefficient `h(x,y)` is made a function
of `y` alone while preserving `x²+y^k` and the ideal `(y^k)`. -/
theorem exists_normalization_equiv (k p : ℕ) (hk : 2 ≤ k) (hp : 3 ≤ p)
    (h : Germ 2) (hc : valueRingHom 2 h ≠ 0) :
    ∃ e : PointedEquivGerm 2, ∃ b : Germ 1,
      valueRingHom 1 b = valueRingHom 2 h ∧
      e.pullbackAlgEquiv (coordinate 0 ^ 2 + coordinate 1 ^ k) =
        coordinate 0 ^ 2 + coordinate 1 ^ k ∧
      e.pullbackAlgEquiv (coordinate 0 ^ p + coordinate 1 ^ k * h) =
        coordinate 0 ^ p + coordinate 1 ^ k * hyperplaneExtension 1 b ∧
      Ideal.map e.forward.pullbackRingHom (Ideal.span {coordinate (1 : Fin 2) ^ k}) =
        Ideal.span {coordinate (1 : Fin 2) ^ k} := by
  obtain ⟨T, v, b, f, hv, hb, hroot, hf0, hf1, hfQ⟩ :=
    exists_normalization_parameters k p (by omega) hp h hc
  obtain ⟨e, he0, he1⟩ := exists_substitution_equiv k hk T v hv
  have hef : e.forward = f := by
    apply ext_components
    intro i
    fin_cases i
    · change e.forward.1.component 0 = f.1.component 0
      rw [he0, hf0]
    · change e.forward.1.component 1 = f.1.component 1
      rw [he1, hf1]
  refine ⟨e, b, hb, substitution_preserves_quadratic k T v hroot e he0 he1, ?_,
    substitution_preserves_coordinate_ideal k v hv e he1⟩
  change e.forward.pullbackRingHom _ = _
  rw [hef]
  exact hfQ

end OnLeConjecture.DTwo.CyclicNormalization
