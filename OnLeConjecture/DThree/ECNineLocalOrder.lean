/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineProjective
public import OnLeConjecture.DTwo.AnalyticCoefficientSpecialization
public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Local orders of the C9 difference section

This file constructs the three analytic branches of the C9 curve at
`[1:0:1:0]`. It computes bounds for the vanishing order of the difference
section on each branch when the form has the exceptional shape
`R₀(x,t³) + c tᴺ`.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

namespace Germ

/-! ## Orders after cubic substitution -/

/-- Cubic substitution multiplies the vanishing order by its exponent. -/
theorem eCNine_substitution_order
    {f : Analytic.Germ 1} {n q : ℕ} (hq : 1 ≤ q)
    (hf : f ≠ 0) (horder : Analytic.Germ.vanishingOrder f = n) :
    Analytic.Germ.vanishingOrder
        (DTwo.Germ.oneVariablePowerSubstitutionRingHom q hq f) = q * n := by
  obtain ⟨m, u, hu, hfactor⟩ :=
    Analytic.Germ.exists_eq_coordinate_pow_mul_unit hf
  have hm : m = n := by
    have hmorder :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    exact ENat.natCast_inj.mp (hmorder.symm.trans horder)
  subst m
  have huMap : IsUnit
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom q hq u) :=
    hu.map _
  apply Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit huMap
  rw [hfactor, map_mul, map_pow,
    DTwo.Germ.oneVariablePowerSubstitutionRingHom_coordinate]
  rw [pow_mul]

/-- The order of a sum with unequal summand orders is their minimum. -/
theorem eCNine_order_add_of_ne {f g : Analytic.Germ 1}
    (h : Analytic.Germ.vanishingOrder f ≠
      Analytic.Germ.vanishingOrder g) :
    Analytic.Germ.vanishingOrder (f + g) =
      min (Analytic.Germ.vanishingOrder f)
        (Analytic.Germ.vanishingOrder g) := by
  by_cases hf : f = 0
  · subst f
    simp
  by_cases hg : g = 0
  · subst g
    simp
  obtain ⟨m, u, hu, hfu⟩ :=
    Analytic.Germ.exists_eq_coordinate_pow_mul_unit hf
  obtain ⟨n, v, hv, hgv⟩ :=
    Analytic.Germ.exists_eq_coordinate_pow_mul_unit hg
  have hfm : Analytic.Germ.vanishingOrder f = m :=
    Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfu
  have hgn : Analytic.Germ.vanishingOrder g = n :=
    Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hv hgv
  have hmn : m ≠ n := by
    intro hmn
    apply h
    rw [hfm, hgn, hmn]
  have order_add_of_lt
      {a b : Analytic.Germ 1} {i j : ℕ}
      {aUnit bUnit : Analytic.Germ 1}
      (haUnit : IsUnit aUnit) (hbUnit : IsUnit bUnit)
      (ha : a = Analytic.Germ.coordinate 0 ^ i * aUnit)
      (hb : b = Analytic.Germ.coordinate 0 ^ j * bUnit)
      (hij : i < j) :
      Analytic.Germ.vanishingOrder (a + b) =
        min (Analytic.Germ.vanishingOrder a)
          (Analytic.Germ.vanishingOrder b) := by
    obtain ⟨d, hdj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
    have hd : d ≠ 0 := by omega
    have hbracket : IsUnit
        (aUnit + Analytic.Germ.coordinate 0 ^ d * bUnit) := by
      apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
      rw [map_add, map_mul, map_pow,
        Analytic.Germ.valueRingHom_coordinate, zero_pow hd, zero_mul,
        add_zero]
      exact Analytic.Germ.valueRingHom_ne_zero_of_isUnit haUnit
    have hab : a + b = Analytic.Germ.coordinate 0 ^ i *
        (aUnit + Analytic.Germ.coordinate 0 ^ d * bUnit) := by
      rw [ha, hb, hdj, pow_add]
      ring
    have habOrder : Analytic.Germ.vanishingOrder (a + b) = i :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
        hbracket hab
    have haOrder : Analytic.Germ.vanishingOrder a = i :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
        haUnit ha
    have hbOrder : Analytic.Germ.vanishingOrder b = j :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
        hbUnit hb
    rw [habOrder, haOrder, hbOrder, min_eq_left]
    exact_mod_cast Nat.le_of_lt hij
  rcases lt_or_gt_of_ne hmn with hmnlt | hmnlt
  · exact order_add_of_lt hu hv hfu hgv hmnlt
  · simpa only [add_comm, min_comm] using
      order_add_of_lt hv hu hgv hfu hmnlt

/-- The branch bracket is a unit when its constant term is nonzero. -/
theorem eCNine_bracket_unit
    {v : Analytic.Germ 1} {kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hkappa : kappa ^ N ≠ 1) :
    IsUnit (1 - Analytic.Germ.constRingHom 1 (kappa ^ N) *
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) ^ N) := by
  apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
  rw [map_sub, map_one, map_mul,
    Analytic.Germ.valueRingHom_const, map_pow]
  rw [DTwo.Germ.oneVariablePowerSubstitutionRingHom,
    PointedMapGerm.valueRingHom_pullback, hv, one_pow]
  exact sub_ne_zero.mpr (by simpa only [mul_one] using hkappa.symm)

/-- If `v(0) = 1` and `1 - v` has order one, then `1 - vᴺ` has order one
for every positive `N`. -/
theorem eCNine_base_exceptional_order
    {v : Analytic.Germ 1} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hN : N ≠ 0)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1) :
    Analytic.Germ.vanishingOrder (1 - v ^ N) = 1 := by
  let geometric : Analytic.Germ 1 := ∑ i ∈ Finset.range N, v ^ i
  have hvalue : Analytic.Germ.valueRingHom 1 geometric = (N : ℂ) := by
    simp [geometric, hv]
  have hNcomplex : (N : ℂ) ≠ 0 := by
    exact_mod_cast hN
  have hunit : IsUnit geometric :=
    Analytic.Germ.isUnit_of_valueRingHom_ne_zero (hvalue.trans_ne hNcomplex)
  have hfactor : (1 - v) * geometric = 1 - v ^ N := by
    exact mul_neg_geom_sum v N
  rw [← hfactor, Analytic.Germ.vanishingOrder_mul, hvorder,
    Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hunit]
  norm_num

/-- Cubic substitution changes the exceptional bracket order from one to
three. -/
theorem eCNine_exceptional_sub_order
    {v : Analytic.Germ 1} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hN : N ≠ 0)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1) :
    Analytic.Germ.vanishingOrder
      (1 - (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) ^ N) = 3 := by
  have hbase := eCNine_base_exceptional_order hv hN hvorder
  have hmap := eCNine_substitution_order (n := 1) (q := 3) (by omega)
    (f := 1 - v ^ N)
  have hne : 1 - v ^ N ≠ 0 := by
    intro hzero
    rw [hzero, Analytic.Germ.vanishingOrder_zero] at hbase
    norm_num at hbase
  have := hmap hne hbase
  rw [map_sub, map_one, map_pow] at this
  norm_num at this
  exact this

/-! ## The local section expression -/

/-- The factor contributed by the pure power on the branch indexed by
`kappa`. -/
@[expose]
noncomputable def eCNineBranchBracket
    (v : Analytic.Germ 1) (kappa : ℂ) (N : ℕ) : Analytic.Germ 1 :=
  1 - Analytic.Germ.constRingHom 1 (kappa ^ N) *
    (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) ^ N

/-- The pure power contribution to the pulled back difference section. -/
@[expose]
noncomputable def eCNinePureBranchTerm
    (v : Analytic.Germ 1) (coefficient kappa : ℂ) (N : ℕ) :
    Analytic.Germ 1 :=
  Analytic.Germ.constRingHom 1 coefficient *
    Analytic.Germ.coordinate 0 ^ N * eCNineBranchBracket v kappa N

/-- Away from the exceptional character, the pure branch term has order
`N`. -/
theorem eCNine_pure_nonexception_order
    {v : Analytic.Germ 1} {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hc : coefficient ≠ 0) (hkappa : kappa ^ N ≠ 1) :
    Analytic.Germ.vanishingOrder
      (eCNinePureBranchTerm v coefficient kappa N) = N := by
  have hcoefficient : IsUnit (Analytic.Germ.constRingHom 1 coefficient) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    simpa using hc
  have hbracket : IsUnit (eCNineBranchBracket v kappa N) := by
    exact eCNine_bracket_unit hv hkappa
  rw [eCNinePureBranchTerm, mul_assoc]
  apply Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
    (hcoefficient.mul hbracket)
  ring

/-- For the exceptional character, the pure branch term has order `N + 3`. -/
theorem eCNine_pure_exception_order
    {v : Analytic.Germ 1} {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hc : coefficient ≠ 0) (hkappa : kappa ^ N = 1)
    (hN : N ≠ 0)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1) :
    Analytic.Germ.vanishingOrder
      (eCNinePureBranchTerm v coefficient kappa N) = N + 3 := by
  have hcoefficient : IsUnit (Analytic.Germ.constRingHom 1 coefficient) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    simpa using hc
  have hcoefficientOrder : Analytic.Germ.vanishingOrder
      (Analytic.Germ.constRingHom 1 coefficient) = 0 :=
    Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hcoefficient
  have hbracket : eCNineBranchBracket v kappa N =
      1 - (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) ^ N := by
    simp [eCNineBranchBracket, hkappa]
  rw [eCNinePureBranchTerm, Analytic.Germ.vanishingOrder_mul,
    Analytic.Germ.vanishingOrder_mul, hcoefficientOrder,
    Analytic.Germ.vanishingOrder_coordinate_pow, hbracket,
    eCNine_exceptional_sub_order hv hN hvorder]
  norm_num

/-- An order produced by cubic substitution cannot equal a degree not
divisible by three. -/
theorem eCNine_sub_order_ne_degree
    {F : Analytic.Germ 1} {N : ℕ} (hnotdiv : ¬ 3 ∣ N) :
    Analytic.Germ.vanishingOrder
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F) ≠ N := by
  by_cases hF : F = 0
  · subst F
    rw [map_zero, Analytic.Germ.vanishingOrder_zero]
    intro htop
    exact ENat.top_ne_natCast N htop
  · obtain ⟨m, u, hu, hfactor⟩ :=
      Analytic.Germ.exists_eq_coordinate_pow_mul_unit hF
    have horder : Analytic.Germ.vanishingOrder F = m :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    have hsub := eCNine_substitution_order (n := m) (q := 3) (by omega) hF horder
    intro heq
    rw [hsub] at heq
    have hnat : 3 * m = N := ENat.natCast_inj.mp heq
    exact hnotdiv ⟨m, hnat.symm⟩

/-- An order produced by cubic substitution cannot equal `N + 3` when `N`
is not divisible by three. -/
theorem eCNine_sub_order_ne_degree_add_three
    {F : Analytic.Germ 1} {N : ℕ} (hnotdiv : ¬ 3 ∣ N) :
    Analytic.Germ.vanishingOrder
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F) ≠ N + 3 := by
  by_cases hF : F = 0
  · subst F
    rw [map_zero, Analytic.Germ.vanishingOrder_zero]
    intro htop
    apply ENat.top_ne_natCast (N + 3)
    norm_num [ENat.natCast_add] at htop ⊢
    exact htop
  · obtain ⟨m, u, hu, hfactor⟩ :=
      Analytic.Germ.exists_eq_coordinate_pow_mul_unit hF
    have horder : Analytic.Germ.vanishingOrder F = m :=
      Analytic.Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    have hsub := eCNine_substitution_order (n := m) (q := 3) (by omega) hF horder
    intro heq
    rw [hsub] at heq
    have hnat : 3 * m = N + 3 := ENat.natCast_inj.mp heq
    apply hnotdiv
    omega

/-- The expression obtained by pulling the hard form difference back to one
local branch. -/
@[expose]
noncomputable def eCNineBranchDifference
    (F v : Analytic.Germ 1) (coefficient kappa : ℂ) (N : ℕ) :
    Analytic.Germ 1 :=
  DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F +
    eCNinePureBranchTerm v coefficient kappa N

/-- The local order is at most `N` on a nonexceptional branch. -/
theorem eCNine_branch_order_nonexception
    {F v : Analytic.Germ 1} {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (hkappa : kappa ^ N ≠ 1) :
    Analytic.Germ.vanishingOrder
      (eCNineBranchDifference F v coefficient kappa N) ≤ N := by
  have hpure := eCNine_pure_nonexception_order hv hc hkappa
  have hne := eCNine_sub_order_ne_degree (F := F) hnotdiv
  rw [eCNineBranchDifference, eCNine_order_add_of_ne (hpure ▸ hne), hpure]
  exact min_le_right _ _

/-- The local order is at most `N + 3` on the exceptional branch. -/
theorem eCNine_branch_order_exception
    {F v : Analytic.Germ 1} {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (hkappa : kappa ^ N = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1) :
    Analytic.Germ.vanishingOrder
      (eCNineBranchDifference F v coefficient kappa N) ≤ N + 3 := by
  have hN : N ≠ 0 := by
    intro hzero
    subst N
    exact hnotdiv (dvd_zero 3)
  have hpure := eCNine_pure_exception_order hv hc hkappa hN hvorder
  have hne := eCNine_sub_order_ne_degree_add_three (F := F) hnotdiv
  rw [eCNineBranchDifference, eCNine_order_add_of_ne (hpure ▸ hne), hpure]
  exact min_le_right _ _

/-! ## The three branch characters -/

/-- An odd power of a cube root of minus one is not one. -/
theorem eCNine_kappa_power_ne_one_of_odd
    {kappa : ℂ} {N : ℕ} (hkappaCube : kappa ^ 3 = -1)
    (hodd : Odd N) : kappa ^ N ≠ 1 := by
  intro hpower
  have hleft : kappa ^ (3 * N) = -1 := by
    calc
      kappa ^ (3 * N) = (kappa ^ 3) ^ N := by rw [pow_mul]
      _ = -1 := by rw [hkappaCube, hodd.neg_one_pow]
  have hright : kappa ^ (3 * N) = 1 := by
    calc
      kappa ^ (3 * N) = kappa ^ (N * 3) := by rw [mul_comm]
      _ = (kappa ^ N) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hpower, one_pow]
  rw [hright] at hleft
  norm_num at hleft

/-- The square of a nonreal cube root of minus one is a primitive cube root
of one. -/
theorem eCNine_square_primitive_cube_root
    {kappa : ℂ} (hkappaCube : kappa ^ 3 = -1)
    (hkappa : kappa ≠ -1) : IsPrimitiveRoot (kappa ^ 2) 3 := by
  have hsquareCube : (kappa ^ 2) ^ 3 = 1 := by
    calc
      (kappa ^ 2) ^ 3 = (kappa ^ 3) ^ 2 := by ring
      _ = 1 := by
        rw [hkappaCube]
        norm_num
  have hsquareNe : kappa ^ 2 ≠ 1 := by
    intro hsquare
    rcases sq_eq_one_iff.mp hsquare with hone | hneg
    · subst kappa
      norm_num at hkappaCube
    · exact hkappa hneg
  apply isPrimitiveRoot_of_mem_nthRootsFinset (p := 3)
    (show Nat.Prime 3 from Nat.prime_three)
  · exact (Polynomial.mem_nthRootsFinset (by norm_num) (1 : ℂ)).mpr
      hsquareCube
  · exact hsquareNe

/-- For even `N` not divisible by three, a cube root of minus one other than
minus one has nontrivial `N`th power. -/
theorem eCNine_kappa_power_ne_one_of_even
    {kappa : ℂ} {N : ℕ} (hkappaCube : kappa ^ 3 = -1)
    (hkappa : kappa ≠ -1) (heven : Even N) (hnotdiv : ¬ 3 ∣ N) :
    kappa ^ N ≠ 1 := by
  intro hpower
  obtain ⟨m, hm⟩ := heven
  have hN : N = 2 * m := by omega
  have hsquare := eCNine_square_primitive_cube_root hkappaCube hkappa
  have hsquarePower : (kappa ^ 2) ^ m = 1 := by
    rw [← pow_mul, ← hN]
    exact hpower
  have hmdiv : 3 ∣ m := (hsquare.pow_eq_one_iff_dvd m).mp hsquarePower
  apply hnotdiv
  rw [hN]
  exact dvd_mul_of_dvd_right hmdiv 2

/-- An even power of minus one is one. -/
theorem eCNine_neg_one_power_eq_one_of_even {N : ℕ} (heven : Even N) :
    (-1 : ℂ) ^ N = 1 := heven.neg_one_pow

/-! ## Construction of the analytic branches -/

/-- There is an analytic solution of
`s(6 + 4s + s²) = 12w` with `s(0) = 0`. -/
theorem eCNine_exists_local_s :
    ∃ s : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 s = 0 ∧
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0 := by
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let factor : Analytic.Germ 1 :=
    Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
      (Analytic.Germ.constRingHom 1 6 +
        Analytic.Germ.constRingHom 1 4 * z + z ^ 2)
  have hfactorValue : Analytic.Germ.valueRingHom 1 factor = (2 : ℂ)⁻¹ := by
    simp [factor, z]
    norm_num
  have hfactorUnit : IsUnit factor := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hfactorValue]
    norm_num
  obtain ⟨e, he⟩ :=
    Analytic.Germ.exists_pointedEquivGerm_component_eq_coordinate_mul_unit
      factor hfactorUnit
  let s : Analytic.Germ 1 := e.inverse.pullbackRingHom z
  refine ⟨s, ?_, ?_⟩
  · change Analytic.Germ.valueRingHom 1
      (e.inverse.pullbackRingHom z) = 0
    rw [Analytic.PointedMapGerm.valueRingHom_pullback]
    exact Analytic.Germ.valueRingHom_coordinate 0
  · have hinverse := e.pullbackRingEquiv.symm_apply_apply z
    change e.inverse.pullbackRingHom (e.forward.pullbackRingHom z) = z at hinverse
    rw [Analytic.PointedMapGerm.pullback_coordinate, he, map_mul] at hinverse
    change s * e.inverse.pullbackRingHom factor = z at hinverse
    have hfactorPullback : e.inverse.pullbackRingHom factor =
        Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
          (Analytic.Germ.constRingHom 1 6 +
            Analytic.Germ.constRingHom 1 4 * s + s ^ 2) := by
      dsimp only [factor]
      rw [map_mul, map_add, map_add, map_mul, map_pow,
        Analytic.PointedMapGerm.pullback_constRingHom,
        Analytic.PointedMapGerm.pullback_constRingHom,
        Analytic.PointedMapGerm.pullback_constRingHom]
    rw [hfactorPullback] at hinverse
    change s *
      (Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2)) = z at hinverse
    have hconstant :
        Analytic.Germ.constRingHom 1 (12 : ℂ) *
          Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ = 1 := by
      rw [← map_mul]
      norm_num
    calc
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
          Analytic.Germ.constRingHom 1 12 *
            (s * (Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
              (Analytic.Germ.constRingHom 1 6 +
                Analytic.Germ.constRingHom 1 4 * s + s ^ 2))) := by
        symm
        calc
          Analytic.Germ.constRingHom 1 12 *
              (s * (Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
                (Analytic.Germ.constRingHom 1 6 +
                  Analytic.Germ.constRingHom 1 4 * s + s ^ 2))) =
            (Analytic.Germ.constRingHom 1 12 *
                Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹) *
              (s * (Analytic.Germ.constRingHom 1 6 +
                Analytic.Germ.constRingHom 1 4 * s + s ^ 2)) := by ring
          _ = s * (Analytic.Germ.constRingHom 1 6 +
                Analytic.Germ.constRingHom 1 4 * s + s ^ 2) := by
            rw [hconstant, one_mul]
      _ = Analytic.Germ.constRingHom 1 12 * z := by rw [hinverse]

/-- The ratio between the two cubic equations is an analytic unit `U`. Its
constant term is one and `1 - U` has order one. -/
theorem eCNine_exists_local_s_U :
    ∃ s U : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 s = 0 ∧
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0 ∧
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2 ∧
      Analytic.Germ.valueRingHom 1 U = 1 ∧
      Analytic.Germ.vanishingOrder (1 - U) = 1 := by
  obtain ⟨s, hsvalue, hsEquation⟩ := eCNine_exists_local_s
  let denominator : Analytic.Germ 1 :=
    Analytic.Germ.constRingHom 1 6 +
      Analytic.Germ.constRingHom 1 4 * s + s ^ 2
  let numerator : Analytic.Germ 1 :=
    Analytic.Germ.constRingHom 1 6 +
      Analytic.Germ.constRingHom 1 8 * s +
        Analytic.Germ.constRingHom 1 3 * s ^ 2
  have hdenominatorValue :
      Analytic.Germ.valueRingHom 1 denominator = 6 := by
    simp [denominator, hsvalue]
  have hdenominatorUnit : IsUnit denominator := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hdenominatorValue]
    norm_num
  let denominatorUnit : (Analytic.Germ 1)ˣ := hdenominatorUnit.unit
  let U : Analytic.Germ 1 :=
    numerator * (↑denominatorUnit⁻¹ : Analytic.Germ 1)
  have hdenominatorUnitSpec :
      (↑denominatorUnit : Analytic.Germ 1) = denominator :=
    hdenominatorUnit.unit_spec
  have hrelation : denominator * U = numerator := by
    calc
      denominator * U =
          numerator * ((↑denominatorUnit : Analytic.Germ 1) *
            (↑denominatorUnit⁻¹ : Analytic.Germ 1)) := by
        simp only [U]
        rw [hdenominatorUnitSpec]
        ring
      _ = numerator := by simp
  have hUvalue : Analytic.Germ.valueRingHom 1 U = 1 := by
    have hvalue := congrArg (Analytic.Germ.valueRingHom 1) hrelation
    simp only [map_mul] at hvalue
    have hnumeratorValue :
        Analytic.Germ.valueRingHom 1 numerator = 6 := by
      simp [numerator, hsvalue]
    rw [hdenominatorValue, hnumeratorValue] at hvalue
    apply mul_left_cancel₀ (by norm_num : (6 : ℂ) ≠ 0)
    simpa using hvalue
  have hsOrder : Analytic.Germ.vanishingOrder s = 1 := by
    have horder := congrArg Analytic.Germ.vanishingOrder hsEquation
    have hconstantUnit : IsUnit (Analytic.Germ.constRingHom 1 (12 : ℂ)) := by
      apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
      norm_num
    rw [Analytic.Germ.vanishingOrder_mul,
      Analytic.Germ.vanishingOrder_mul,
      Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hdenominatorUnit,
      Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hconstantUnit,
      Analytic.Germ.vanishingOrder_coordinate] at horder
    norm_num at horder ⊢
    exact horder
  have hlinearUnit : IsUnit
      (Analytic.Germ.constRingHom 1 4 +
        Analytic.Germ.constRingHom 1 2 * s) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    simp [hsvalue]
  have hfactor : denominator * (U - 1) =
      s * (Analytic.Germ.constRingHom 1 4 +
        Analytic.Germ.constRingHom 1 2 * s) := by
    have hconstantEight : Analytic.Germ.constRingHom 1 (8 : ℂ) =
        Analytic.Germ.constRingHom 1 4 +
          Analytic.Germ.constRingHom 1 4 := by
      rw [← map_add]
      norm_num
    have hconstantThree : Analytic.Germ.constRingHom 1 (3 : ℂ) =
        1 + Analytic.Germ.constRingHom 1 2 := by
      calc
        Analytic.Germ.constRingHom 1 (3 : ℂ) =
            Analytic.Germ.constRingHom 1 ((1 : ℂ) + 2) := by norm_num
        _ = Analytic.Germ.constRingHom 1 1 +
            Analytic.Germ.constRingHom 1 2 := map_add _ _ _
        _ = 1 + Analytic.Germ.constRingHom 1 2 := by rw [map_one]
    rw [mul_sub, hrelation]
    simp only [mul_one]
    dsimp only [denominator, numerator]
    rw [hconstantEight, hconstantThree]
    ring
  have hUsubOrder : Analytic.Germ.vanishingOrder (U - 1) = 1 := by
    have horder := congrArg Analytic.Germ.vanishingOrder hfactor
    rw [Analytic.Germ.vanishingOrder_mul,
      Analytic.Germ.vanishingOrder_mul,
      Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hdenominatorUnit,
      Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hlinearUnit,
      hsOrder] at horder
    norm_num at horder ⊢
    exact horder
  have hOneSubOrder : Analytic.Germ.vanishingOrder (1 - U) = 1 := by
    calc
      Analytic.Germ.vanishingOrder (1 - U) =
          Analytic.Germ.vanishingOrder
            ((-1 : Analytic.Germ 1) * (U - 1)) := by
        congr 1
        ring
      _ = Analytic.Germ.vanishingOrder (-1 : Analytic.Germ 1) +
          Analytic.Germ.vanishingOrder (U - 1) :=
        Analytic.Germ.vanishingOrder_mul _ _
      _ = Analytic.Germ.vanishingOrder (U - 1) := by
        rw [Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr
          isUnit_neg_one, zero_add]
      _ = 1 := hUsubOrder
  exact ⟨s, U, hsvalue, hsEquation, hrelation, hUvalue, hOneSubOrder⟩

/-- A unit with value one and nonzero first jet has a normalized analytic
cube root with the same property. -/
theorem eCNine_exists_normalized_cube_root
    {U : Analytic.Germ 1}
    (hUvalue : Analytic.Germ.valueRingHom 1 U = 1)
    (hUorder : Analytic.Germ.vanishingOrder (1 - U) = 1) :
    ∃ v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 := by
  have hUunit : IsUnit U := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hUvalue]
    exact one_ne_zero
  obtain ⟨vZero, hvZeroUnit, hvZeroCube⟩ :=
    Analytic.Germ.exists_isUnit_pow_eq U hUunit (by norm_num : 3 ≠ 0)
  let alpha : ℂ := Analytic.Germ.valueRingHom 1 vZero
  have halphaNe : alpha ≠ 0 :=
    Analytic.Germ.valueRingHom_ne_zero_of_isUnit hvZeroUnit
  have halphaCube : alpha ^ 3 = 1 := by
    have hvalue := congrArg (Analytic.Germ.valueRingHom 1) hvZeroCube
    simpa only [map_pow, hUvalue] using hvalue
  let v : Analytic.Germ 1 :=
    Analytic.Germ.constRingHom 1 alpha⁻¹ * vZero
  have hvValue : Analytic.Germ.valueRingHom 1 v = 1 := by
    simp only [v, map_mul, Analytic.Germ.valueRingHom_const, alpha]
    exact inv_mul_cancel₀ halphaNe
  have hvCube : v ^ 3 = U := by
    dsimp only [v]
    rw [mul_pow, ← map_pow, hvZeroCube]
    have halphaInvCube : alpha⁻¹ ^ 3 = 1 := by
      rw [inv_pow, halphaCube, inv_one]
    rw [halphaInvCube, map_one, one_mul]
  let geometric : Analytic.Germ 1 := ∑ i ∈ Finset.range 3, v ^ i
  have hgeometricValue :
      Analytic.Germ.valueRingHom 1 geometric = (3 : ℂ) := by
    simp [geometric, hvValue]
  have hgeometricUnit : IsUnit geometric := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hgeometricValue]
    norm_num
  have hfactor : (1 - v) * geometric = 1 - v ^ 3 :=
    mul_neg_geom_sum v 3
  have hvOrder : Analytic.Germ.vanishingOrder (1 - v) = 1 := by
    have horder := congrArg Analytic.Germ.vanishingOrder hfactor
    rw [Analytic.Germ.vanishingOrder_mul,
      Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hgeometricUnit,
      hvCube, hUorder] at horder
    norm_num at horder ⊢
    exact horder
  exact ⟨v, hvValue, hvCube, hvOrder⟩

/-- The analytic functions needed for all three local branch
parametrizations exist simultaneously. -/
theorem eCNine_exists_local_branch_data :
    ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 s = 0 ∧
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0 ∧
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2 ∧
      Analytic.Germ.valueRingHom 1 U = 1 ∧
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 := by
  obtain ⟨s, U, hsvalue, hsEquation, hrelation, hUvalue, hUorder⟩ :=
    eCNine_exists_local_s_U
  obtain ⟨v, hvValue, hvCube, hvOrder⟩ :=
    eCNine_exists_normalized_cube_root hUvalue hUorder
  exact ⟨s, U, v, hsvalue, hsEquation, hrelation, hUvalue,
    hvValue, hvCube, hvOrder⟩

/-- The local parametrization indexed by a cube root `kappa` of minus one. -/
@[expose]
noncomputable def eCNineLocalPoint
    (s v : Analytic.Germ 1) (kappa : ℂ) : Fin 4 → Analytic.Germ 1 :=
  ![1,
    Analytic.Germ.coordinate 0,
    1 + DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s,
    Analytic.Germ.constRingHom 1 kappa * Analytic.Germ.coordinate 0 *
      DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v]

/-- Every local parametrization is based at the affine representative
`(1,0,1,0)` of `eCNinePZero`. -/
theorem eCNineLocalPoint_value
    {s v : Analytic.Germ 1} {kappa : ℂ}
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hv : Analytic.Germ.valueRingHom 1 v = 1) :
    (fun i ↦ Analytic.Germ.valueRingHom 1
      (eCNineLocalPoint s v kappa i)) = ![1, 0, 1, 0] := by
  have hsSub : Analytic.Germ.valueRingHom 1
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s) = 0 := by
    rw [DTwo.Germ.oneVariablePowerSubstitutionRingHom,
      PointedMapGerm.valueRingHom_pullback, hs]
  have hvSub : Analytic.Germ.valueRingHom 1
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) = 1 := by
    rw [DTwo.Germ.oneVariablePowerSubstitutionRingHom,
      PointedMapGerm.valueRingHom_pullback, hv]
  funext i
  fin_cases i <;> simp [eCNineLocalPoint, hsSub, hvSub]

/-- Distinct branch characters give distinct local parametrizations. -/
theorem eCNineLocalPoint_ne_of_kappa_ne
    {s v : Analytic.Germ 1} {kappa mu : ℂ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hne : kappa ≠ mu) :
    eCNineLocalPoint s v kappa ≠ eCNineLocalPoint s v mu := by
  intro hpoint
  have hcoord := congrFun hpoint (3 : Fin 4)
  have hvSubValue : Analytic.Germ.valueRingHom 1
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) = 1 := by
    rw [DTwo.Germ.oneVariablePowerSubstitutionRingHom,
      PointedMapGerm.valueRingHom_pullback, hv]
  have hvSubUnit : IsUnit
      (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hvSubValue]
    exact one_ne_zero
  let factor : Analytic.Germ 1 := Analytic.Germ.coordinate 0 *
    DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v
  have hfactor : factor ≠ 0 := by
    exact mul_ne_zero Analytic.Germ.coordinate_zero_ne_zero hvSubUnit.ne_zero
  have hproduct : Analytic.Germ.constRingHom 1 kappa * factor =
      Analytic.Germ.constRingHom 1 mu * factor := by
    simpa [eCNineLocalPoint, factor, mul_assoc] using hcoord
  have hconstant : Analytic.Germ.constRingHom 1 kappa =
      Analytic.Germ.constRingHom 1 mu := mul_right_cancel₀ hfactor hproduct
  apply hne
  have hvalue := congrArg (Analytic.Germ.valueRingHom 1) hconstant
  simpa using hvalue

set_option linter.flexible false in
/-- The local parametrization satisfies both defining equations of the C9
curve. -/
theorem eCNineLocalPoint_C9
    {s U v : Analytic.Germ 1} {kappa : ℂ}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (hkappaCube : kappa ^ 3 = -1) :
    MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
        (eCNineLocalPoint s v kappa) eCNineFirstPolynomial = 0 ∧
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
        (eCNineLocalPoint s v kappa) eCNineSecondPolynomial = 0 := by
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let sSub := sub s
  let USub := sub U
  let vSub := sub v
  have hsSub := congrArg sub hsEquation
  have hrelationSub := congrArg sub hrelation
  have hvCubeSub := congrArg sub hvCube
  have hsSubEquation :
      sSub * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) =
        Analytic.Germ.constRingHom 1 12 * z ^ 3 := by
    simpa [sub, sSub, z] using hsSub
  have hrelationSubEquation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) * USub =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * sSub +
            Analytic.Germ.constRingHom 1 3 * sSub ^ 2 := by
    simpa [sub, sSub, USub] using hrelationSub
  have hvCubeSubEquation : vSub ^ 3 = USub := by
    simpa [sub, vSub, USub] using hvCubeSub
  have hweighted :
      Analytic.Germ.constRingHom 1 12 * z ^ 3 * USub =
        sSub * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * sSub +
            Analytic.Germ.constRingHom 1 3 * sSub ^ 2) := by
    calc
      Analytic.Germ.constRingHom 1 12 * z ^ 3 * USub =
          (sSub * (Analytic.Germ.constRingHom 1 6 +
            Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2)) * USub := by
        rw [hsSubEquation]
      _ = sSub * ((Analytic.Germ.constRingHom 1 6 +
            Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) * USub) := by
        rw [mul_assoc]
      _ = _ := by rw [hrelationSubEquation]
  have hc2 : Analytic.Germ.constRingHom 1 (2 : ℂ) = (2 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 2
  have hc3 : Analytic.Germ.constRingHom 1 (3 : ℂ) = (3 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 3
  have hc4 : Analytic.Germ.constRingHom 1 (4 : ℂ) = (4 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 4
  have hc6 : Analytic.Germ.constRingHom 1 (6 : ℂ) = (6 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 6
  have hc8 : Analytic.Germ.constRingHom 1 (8 : ℂ) = (8 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 8
  have hc12 : Analytic.Germ.constRingHom 1 (12 : ℂ) = (12 : Analytic.Germ 1) := by
    exact map_ofNat (Analytic.Germ.constRingHom 1) 12
  constructor
  · simp [eCNineFirstPolynomial, eCNineLocalPoint, eCNineX, eCNineT,
      eCNineCapitalX]
    change Analytic.Germ.constRingHom 1 12 * z ^ 3 +
      -(sSub * ((1 + sSub) ^ 2 +
        Analytic.Germ.constRingHom 1 2 * (1 + sSub) +
        Analytic.Germ.constRingHom 1 3)) = 0
    rw [hc6, hc4, hc12] at hsSubEquation
    rw [hc12, hc2, hc3]
    linear_combination -hsSubEquation
  · simp [eCNineSecondPolynomial, eCNineLocalPoint, eCNineX,
      eCNineCapitalX, eCNineCapitalT]
    change Analytic.Germ.constRingHom 1 12 *
        (Analytic.Germ.constRingHom 1 kappa * z * vSub) ^ 3 +
      sSub * (Analytic.Germ.constRingHom 1 3 * (1 + sSub) ^ 2 +
        Analytic.Germ.constRingHom 1 2 * (1 + sSub) + 1) = 0
    have hkappaGerm :
        (Analytic.Germ.constRingHom 1 kappa) ^ 3 = -1 := by
      rw [← map_pow, hkappaCube, map_neg, map_one]
    rw [mul_pow, mul_pow, hkappaGerm, hvCubeSubEquation]
    rw [hc12, hc6, hc8, hc3] at hweighted
    rw [hc12, hc3, hc2]
    linear_combination -hweighted

/-! ## Pullback of the hard form section -/

/-- Evaluation of the cube substitution at analytic germs replaces `w` by
`t³`. -/
theorem eCNine_sourceCube_eval_germ
    (Rzero : ESourceRing ℂ) (x t : Analytic.Germ 1) :
    MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1) ![x, t]
        (eSourceCubeSubstitutionForm Rzero) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
        (fun
          | ESourceCoordinate.x => x
          | ESourceCoordinate.w => t ^ 3) Rzero := by
  let left : ESourceRing ℂ →ₐ[ℂ] Analytic.Germ 1 :=
    (MvPolynomial.aeval ![x, t]).comp eSourceCubeSubstitutionForm
  let right : ESourceRing ℂ →ₐ[ℂ] Analytic.Germ 1 :=
    MvPolynomial.aeval fun
      | ESourceCoordinate.x => x
      | ESourceCoordinate.w => t ^ 3
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | x =>
      dsimp only [left, right, AlgHom.comp_apply]
      rw [MvPolynomial.aeval_X]
      change MvPolynomial.aeval ![x, t]
          (eSourceCubeSubstitutionForm (eSourceX ℂ)) = x
      rw [eSourceCubeSubstitutionForm_x]
      simp [formX]
    | w =>
      dsimp only [left, right, AlgHom.comp_apply]
      rw [MvPolynomial.aeval_X]
      change MvPolynomial.aeval ![x, t]
          (eSourceCubeSubstitutionForm (eSourceW ℂ)) = t ^ 3
      rw [eSourceCubeSubstitutionForm_w]
      simp [formT]
  exact AlgHom.congr_fun heq Rzero

/-- Cubic substitution commutes with polynomial evaluation at analytic
germs. -/
theorem eCNine_powerSub_eval₂
    (P : ESourceRing ℂ) (g : ESourceCoordinate → Analytic.Germ 1) :
    DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
        (MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1) g P) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
        (fun i ↦ DTwo.Germ.oneVariablePowerSubstitutionRingHom 3
          (by omega) (g i)) P := by
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  have hconst : sub.comp (Analytic.Germ.constRingHom 1) =
      Analytic.Germ.constRingHom 1 := by
    apply DFunLike.ext _ _
    intro c
    exact DTwo.Germ.oneVariablePowerSubstitutionRingHom_const 3 (by omega) c
  rw [MvPolynomial.hom_eval₂]
  rw [hconst]

/-- The difference of the invariant part before cubic substitution. -/
@[expose]
noncomputable def eCNineLocalInvariantDifference
    (Rzero : ESourceRing ℂ) (s U : Analytic.Germ 1) : Analytic.Germ 1 :=
  MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
      (fun
        | ESourceCoordinate.x => 1
        | ESourceCoordinate.w => Analytic.Germ.coordinate 0) Rzero -
    MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
      (fun
        | ESourceCoordinate.x => 1 + s
        | ESourceCoordinate.w => -Analytic.Germ.coordinate 0 * U) Rzero

set_option linter.flexible false in
/-- Pullback of the section defined by `R₀(x,t³) + c tᴺ` is the branch
difference expression used in the order estimates. -/
theorem eCNine_local_section_eq_branchDifference
    (Rzero : ESourceRing ℂ) (s U v : Analytic.Germ 1)
    (coefficient kappa : ℂ) (N : ℕ)
    (hvCube : v ^ 3 = U) (hkappaCube : kappa ^ 3 = -1) :
    MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
        (eCNineLocalPoint s v kappa)
        (eCNineDifferenceSection
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)) =
      eCNineBranchDifference
        (eCNineLocalInvariantDifference Rzero s U) v coefficient kappa N := by
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let sSub := sub s
  let USub := sub U
  let vSub := sub v
  let TSub := Analytic.Germ.constRingHom 1 kappa * z * vSub
  have hvCubeSub := congrArg sub hvCube
  have hvCubeSubEquation : vSub ^ 3 = USub := by
    simpa [sub, vSub, USub] using hvCubeSub
  have hkappaGerm :
      (Analytic.Germ.constRingHom 1 kappa) ^ 3 = -1 := by
    rw [← map_pow, hkappaCube, map_neg, map_one]
  have hTCube : TSub ^ 3 = -z ^ 3 * USub := by
    dsimp only [TSub]
    rw [mul_pow, mul_pow, hkappaGerm, hvCubeSubEquation]
    ring
  have hsectionEval :
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          (eCNineLocalPoint s v kappa)
          (eCNineDifferenceSection
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) =
        MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1) ![1, z]
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N) -
          MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
            ![1 + sSub, TSub]
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N) := by
    change MvPolynomial.aeval (eCNineLocalPoint s v kappa)
        (MvPolynomial.aeval ![eCNineX, eCNineT]
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N) -
          MvPolynomial.aeval ![eCNineCapitalX, eCNineCapitalT]
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) = _
    rw [map_sub]
    congr 1
    · rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
      apply congrArg (fun g : Fin 2 → Analytic.Germ 1 ↦
        MvPolynomial.aeval g
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N))
      funext i
      fin_cases i
      · simp [eCNineLocalPoint, eCNineX, z]
      · simp [eCNineLocalPoint, eCNineT, z]
    · rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
      apply congrArg (fun g : Fin 2 → Analytic.Germ 1 ↦
        MvPolynomial.aeval g
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N))
      funext i
      fin_cases i
      · simp [eCNineCapitalX, eCNineLocalPoint, sSub]
        exact rfl
      · simp [eCNineCapitalT, eCNineLocalPoint, TSub, vSub]
        exact rfl
  rw [hsectionEval]
  rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add,
    eCNine_sourceCube_eval_germ, eCNine_sourceCube_eval_germ]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, formT,
    eCNineBranchDifference, eCNinePureBranchTerm, eCNineBranchBracket]
  have hFsub : sub (eCNineLocalInvariantDifference Rzero s U) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          (fun
            | ESourceCoordinate.x => 1
            | ESourceCoordinate.w => z ^ 3) Rzero -
        MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          (fun
            | ESourceCoordinate.x => 1 + sSub
            | ESourceCoordinate.w => -z ^ 3 * USub) Rzero := by
    dsimp only [eCNineLocalInvariantDifference]
    rw [map_sub]
    congr 1
    · rw [eCNine_powerSub_eval₂]
      congr
      funext i
      cases i <;> simp [z]
    · rw [eCNine_powerSub_eval₂]
      congr
      funext i
      cases i <;> simp [sub, z, sSub, USub]
  change _ = sub (eCNineLocalInvariantDifference Rzero s U) + _
  rw [hFsub, hTCube]
  have hTPow : TSub ^ N =
      Analytic.Germ.constRingHom 1 (kappa ^ N) * z ^ N * vSub ^ N := by
    dsimp only [TSub]
    rw [mul_pow, mul_pow, ← map_pow]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [hTPow]
  change _ = _ + Analytic.Germ.constRingHom 1 coefficient * z ^ N *
    (1 - Analytic.Germ.constRingHom 1 (kappa ^ N) * vSub ^ N)
  ring

/-- The three cube roots of minus one obtained from a primitive cube root of
one. -/
@[expose]
noncomputable def eCNineBranchKappa (omega : ℂ) : Fin 3 → ℂ :=
  ![-1, -omega, -(omega ^ 2)]

/-- Every branch character has cube equal to minus one. -/
theorem eCNineBranchKappa_cube {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) : eCNineBranchKappa omega i ^ 3 = -1 := by
  have hc : omega ^ 3 = 1 := homega.pow_eq_one
  fin_cases i
  · norm_num [eCNineBranchKappa]
  · norm_num [eCNineBranchKappa, neg_pow, hc]
  · norm_num [eCNineBranchKappa, neg_pow]
    rw [show (omega ^ 2) ^ 3 = (omega ^ 3) ^ 2 by ring, hc]
    norm_num

/-- The three branch characters are pairwise distinct. -/
theorem eCNineBranchKappa_pairwise_ne {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    eCNineBranchKappa omega 0 ≠ eCNineBranchKappa omega 1 ∧
      eCNineBranchKappa omega 0 ≠ eCNineBranchKappa omega 2 ∧
      eCNineBranchKappa omega 1 ≠ eCNineBranchKappa omega 2 := by
  have hone : omega ≠ 1 := homega.ne_one (by norm_num)
  have hsquare : omega ^ 2 ≠ 1 :=
    (homega.pow_eq_one_iff_dvd 2).not.mpr (by norm_num)
  have homegaZero : omega ≠ 0 := by
    intro hzero
    have hc : omega ^ 3 = 1 := homega.pow_eq_one
    rw [hzero, zero_pow (by norm_num : 3 ≠ 0)] at hc
    norm_num at hc
  have hlinear : omega ≠ omega ^ 2 := by
    intro h
    apply hone
    apply mul_left_cancel₀ homegaZero
    calc
      omega * omega = omega ^ 2 := (pow_two omega).symm
      _ = omega := h.symm
      _ = omega * 1 := (mul_one omega).symm
  constructor
  · simpa [eCNineBranchKappa] using hone.symm
  constructor
  · simpa [eCNineBranchKappa] using hsquare.symm
  · simpa [eCNineBranchKappa] using hlinear

/-- The assignment of the three branch characters is injective. -/
theorem eCNineBranchKappa_injective
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    Function.Injective (eCNineBranchKappa omega) := by
  have hne := eCNineBranchKappa_pairwise_ne homega
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The three explicit parametrizations are based at `eCNinePZero` and
satisfy both C9 equations. -/
theorem eCNine_exists_three_local_branches
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      Function.Injective
        (fun i ↦ eCNineLocalPoint s v (eCNineBranchKappa omega i)) ∧
      ∀ i : Fin 3,
        (fun j ↦ Analytic.Germ.valueRingHom 1
          (eCNineLocalPoint s v (eCNineBranchKappa omega i) j)) =
            ![1, 0, 1, 0] ∧
        MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
            (eCNineLocalPoint s v (eCNineBranchKappa omega i))
            eCNineFirstPolynomial = 0 ∧
          MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
            (eCNineLocalPoint s v (eCNineBranchKappa omega i))
            eCNineSecondPolynomial = 0 := by
  obtain ⟨s, U, v, hsvalue, hsEquation, hrelation, _hUvalue,
      hv, hvCube, hvorder⟩ := eCNine_exists_local_branch_data
  refine ⟨s, U, v, hv, hvCube, hvorder, ?_, ?_⟩
  · intro i j hij
    apply eCNineBranchKappa_injective homega
    by_contra hne
    exact eCNineLocalPoint_ne_of_kappa_ne hv hne hij
  intro i
  refine ⟨eCNineLocalPoint_value hsvalue hv, ?_⟩
  exact eCNineLocalPoint_C9 hsEquation hrelation hvCube
    (eCNineBranchKappa_cube homega i)

/-- In odd degree, the sum of the orders on three branches is at most
`3N`. -/
theorem eCNine_odd_three_branch_order_sum_le
    {F v : Analytic.Germ 1} {coefficient kappaZero kappaOne kappaTwo : ℂ}
    {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N)
    (hkappaZero : kappaZero ^ 3 = -1)
    (hkappaOne : kappaOne ^ 3 = -1)
    (hkappaTwo : kappaTwo ^ 3 = -1) :
    Analytic.Germ.vanishingOrder
          (eCNineBranchDifference F v coefficient kappaZero N) +
        Analytic.Germ.vanishingOrder
          (eCNineBranchDifference F v coefficient kappaOne N) +
      Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v coefficient kappaTwo N) ≤
      ((3 * N : ℕ) : ℕ∞) := by
  have hzero := eCNine_branch_order_nonexception (F := F) hv hc hnotdiv
    (eCNine_kappa_power_ne_one_of_odd hkappaZero hodd)
  have hone := eCNine_branch_order_nonexception (F := F) hv hc hnotdiv
    (eCNine_kappa_power_ne_one_of_odd hkappaOne hodd)
  have htwo := eCNine_branch_order_nonexception (F := F) hv hc hnotdiv
    (eCNine_kappa_power_ne_one_of_odd hkappaTwo hodd)
  calc
    _ ≤ (N : ℕ∞) + N + N := add_le_add (add_le_add hzero hone) htwo
    _ = ((3 * N : ℕ) : ℕ∞) := by
      norm_num [ENat.natCast_mul]
      ring

/-- In even degree, one exceptional branch adds at most three to the sum of
the three branch orders. -/
theorem eCNine_even_three_branch_order_sum_le
    {F v : Analytic.Germ 1} {coefficient kappaOne kappaTwo : ℂ}
    {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N)
    (hkappaOneCube : kappaOne ^ 3 = -1) (hkappaOne : kappaOne ≠ -1)
    (hkappaTwoCube : kappaTwo ^ 3 = -1) (hkappaTwo : kappaTwo ≠ -1) :
    Analytic.Germ.vanishingOrder
          (eCNineBranchDifference F v coefficient (-1) N) +
        Analytic.Germ.vanishingOrder
          (eCNineBranchDifference F v coefficient kappaOne N) +
      Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v coefficient kappaTwo N) ≤
      ((3 * N + 3 : ℕ) : ℕ∞) := by
  have hzero := eCNine_branch_order_exception (F := F) hv hc hnotdiv
    (eCNine_neg_one_power_eq_one_of_even heven) hvorder
  have hone := eCNine_branch_order_nonexception (F := F) hv hc hnotdiv
    (eCNine_kappa_power_ne_one_of_even hkappaOneCube hkappaOne heven hnotdiv)
  have htwo := eCNine_branch_order_nonexception (F := F) hv hc hnotdiv
    (eCNine_kappa_power_ne_one_of_even hkappaTwoCube hkappaTwo heven hnotdiv)
  calc
    _ ≤ ((N + 3 : ℕ) : ℕ∞) + N + N :=
      add_le_add (add_le_add hzero hone) htwo
    _ = ((3 * N + 3 : ℕ) : ℕ∞) := by
      norm_num [ENat.natCast_mul, ENat.natCast_add]
      ring

/-- Pullback of the hard form difference section to a local C9 branch. -/
@[expose]
noncomputable def eCNineLocalSectionPullback
    (Rzero : ESourceRing ℂ) (s v : Analytic.Germ 1)
    (coefficient kappa : ℂ) (N : ℕ) : Analytic.Germ 1 :=
  MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
    (eCNineLocalPoint s v kappa)
    (eCNineDifferenceSection
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N))

/-- The pulled back section equals the branch difference expression. -/
theorem eCNineLocalSectionPullback_eq_branchDifference
    (Rzero : ESourceRing ℂ) (s U v : Analytic.Germ 1)
    (coefficient kappa : ℂ) (N : ℕ)
    (hvCube : v ^ 3 = U) (hkappaCube : kappa ^ 3 = -1) :
    eCNineLocalSectionPullback Rzero s v coefficient kappa N =
      eCNineBranchDifference
        (eCNineLocalInvariantDifference Rzero s U) v coefficient kappa N := by
  rw [eCNineLocalSectionPullback]
  exact eCNine_local_section_eq_branchDifference
    Rzero s U v coefficient kappa N hvCube hkappaCube

/-- In odd degree, the pulled back section has order at most `N` on every
branch. -/
theorem eCNineLocalSection_odd_order_le
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U) (hc : coefficient ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N)
    (hkappaCube : kappa ^ 3 = -1) :
    Analytic.Germ.vanishingOrder
      (eCNineLocalSectionPullback Rzero s v coefficient kappa N) ≤ N := by
  rw [eCNineLocalSectionPullback_eq_branchDifference Rzero s U v coefficient kappa N
    hvCube hkappaCube]
  exact eCNine_branch_order_nonexception (F :=
    eCNineLocalInvariantDifference Rzero s U) hv hc hnotdiv
      (eCNine_kappa_power_ne_one_of_odd hkappaCube hodd)

/-- In even degree, the section has order at most `N + 3` on the branch with
character minus one. -/
theorem eCNineLocalSection_even_exceptional_order_le
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N) :
    Analytic.Germ.vanishingOrder
      (eCNineLocalSectionPullback Rzero s v coefficient (-1) N) ≤ N + 3 := by
  rw [eCNineLocalSectionPullback_eq_branchDifference Rzero s U v coefficient (-1) N
    hvCube (by norm_num)]
  exact eCNine_branch_order_exception (F :=
    eCNineLocalInvariantDifference Rzero s U) hv hc hnotdiv
      (eCNine_neg_one_power_eq_one_of_even heven) hvorder

/-- In even degree, the section has order at most `N` on either remaining
branch. -/
theorem eCNineLocalSection_even_nonexceptional_order_le
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U) (hc : coefficient ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) (heven : Even N)
    (hkappaCube : kappa ^ 3 = -1) (hkappa : kappa ≠ -1) :
    Analytic.Germ.vanishingOrder
      (eCNineLocalSectionPullback Rzero s v coefficient kappa N) ≤ N := by
  rw [eCNineLocalSectionPullback_eq_branchDifference Rzero s U v coefficient kappa N
    hvCube hkappaCube]
  exact eCNine_branch_order_nonexception (F :=
    eCNineLocalInvariantDifference Rzero s U) hv hc hnotdiv
      (eCNine_kappa_power_ne_one_of_even
        hkappaCube hkappa heven hnotdiv)

/-- The sum of the three pulled back section orders is at most `3N` when
`N` is odd. -/
theorem eCNineLocalSection_odd_three_branch_order_sum_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U) (hc : coefficient ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N) :
    Analytic.Germ.vanishingOrder
          (eCNineLocalSectionPullback Rzero s v coefficient
            (eCNineBranchKappa omega 0) N) +
        Analytic.Germ.vanishingOrder
          (eCNineLocalSectionPullback Rzero s v coefficient
            (eCNineBranchKappa omega 1) N) +
      Analytic.Germ.vanishingOrder
        (eCNineLocalSectionPullback Rzero s v coefficient
          (eCNineBranchKappa omega 2) N) ≤
      ((3 * N : ℕ) : ℕ∞) := by
  have hzero := eCNineLocalSection_odd_order_le (Rzero := Rzero) (s := s)
    hv hvCube hc hnotdiv hodd
    (eCNineBranchKappa_cube homega 0)
  have hone := eCNineLocalSection_odd_order_le (Rzero := Rzero) (s := s)
    hv hvCube hc hnotdiv hodd
    (eCNineBranchKappa_cube homega 1)
  have htwo := eCNineLocalSection_odd_order_le (Rzero := Rzero) (s := s)
    hv hvCube hc hnotdiv hodd
    (eCNineBranchKappa_cube homega 2)
  calc
    _ ≤ (N : ℕ∞) + N + N := add_le_add (add_le_add hzero hone) htwo
    _ = ((3 * N : ℕ) : ℕ∞) := by
      norm_num [ENat.natCast_mul]
      ring

/-- The sum of the three pulled back section orders is at most `3N + 3` when
`N` is even. -/
theorem eCNineLocalSection_even_three_branch_order_sum_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N) :
    Analytic.Germ.vanishingOrder
          (eCNineLocalSectionPullback Rzero s v coefficient
            (eCNineBranchKappa omega 0) N) +
        Analytic.Germ.vanishingOrder
          (eCNineLocalSectionPullback Rzero s v coefficient
            (eCNineBranchKappa omega 1) N) +
      Analytic.Germ.vanishingOrder
        (eCNineLocalSectionPullback Rzero s v coefficient
          (eCNineBranchKappa omega 2) N) ≤
      ((3 * N + 3 : ℕ) : ℕ∞) := by
  have hroots := eCNineBranchKappa_pairwise_ne homega
  have hzero : Analytic.Germ.vanishingOrder
      (eCNineLocalSectionPullback Rzero s v coefficient
        (eCNineBranchKappa omega 0) N) ≤ N + 3 := by
    simpa [eCNineBranchKappa] using
      eCNineLocalSection_even_exceptional_order_le (Rzero := Rzero) (s := s)
        hv hvCube hvorder hc hnotdiv heven
  have hone := eCNineLocalSection_even_nonexceptional_order_le
    (Rzero := Rzero) (s := s) hv hvCube hc
    hnotdiv heven (eCNineBranchKappa_cube homega 1) hroots.1.symm
  have htwo := eCNineLocalSection_even_nonexceptional_order_le
    (Rzero := Rzero) (s := s) hv hvCube hc
    hnotdiv heven (eCNineBranchKappa_cube homega 2) hroots.2.1.symm
  calc
    _ ≤ ((N + 3 : ℕ) : ℕ∞) + N + N :=
      add_le_add (add_le_add hzero hone) htwo
    _ = ((3 * N + 3 : ℕ) : ℕ∞) := by
      norm_num [ENat.natCast_mul, ENat.natCast_add]
      ring

/-- The sum of the section orders on the three explicit parametrizations
through `eCNinePZero`. -/
@[expose]
noncomputable def eCNinePZeroExplicitBranchContribution
    (omega : ℂ) (Rzero : ESourceRing ℂ)
    (s v : Analytic.Germ 1) (coefficient : ℂ) (N : ℕ) : ℕ∞ :=
  Analytic.Germ.vanishingOrder
        (eCNineLocalSectionPullback Rzero s v coefficient
          (eCNineBranchKappa omega 0) N) +
      Analytic.Germ.vanishingOrder
        (eCNineLocalSectionPullback Rzero s v coefficient
          (eCNineBranchKappa omega 1) N) +
    Analytic.Germ.vanishingOrder
      (eCNineLocalSectionPullback Rzero s v coefficient
        (eCNineBranchKappa omega 2) N)

/-- In odd degree, the explicit branch contribution at `eCNinePZero` is at
most `3N`. -/
theorem eCNinePZeroExplicitBranchContribution_odd_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U) (hc : coefficient ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N) :
    eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N : ℕ) : ℕ∞) := by
  simpa only [eCNinePZeroExplicitBranchContribution] using
    eCNineLocalSection_odd_three_branch_order_sum_le
      homega hv hvCube hc hnotdiv hodd

/-- In even degree, the explicit branch contribution at `eCNinePZero` is at
most `3N + 3`. -/
theorem eCNinePZeroExplicitBranchContribution_even_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N) :
    eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N + 3 : ℕ) : ℕ∞) := by
  simpa only [eCNinePZeroExplicitBranchContribution] using
    eCNineLocalSection_even_three_branch_order_sum_le
      homega hv hvCube hvorder hc hnotdiv heven

/-- The odd branch bound is strictly below the expected degree `9N` of the
restricted projective section. -/
theorem eCNine_three_mul_lt_nine_mul
    {N : ℕ} (hnotdiv : ¬ 3 ∣ N) : 3 * N < 9 * N := by
  have hN : 0 < N := by
    by_contra hzero
    apply hnotdiv
    simp_all
  omega

/-- The even branch bound is strictly below the expected degree `9N` of the
restricted projective section. -/
theorem eCNine_three_mul_add_three_lt_nine_mul
    {N : ℕ} (hnotdiv : ¬ 3 ∣ N) : 3 * N + 3 < 9 * N := by
  have hN : 0 < N := by
    by_contra hzero
    apply hnotdiv
    simp_all
  omega

/-- In odd degree, the explicit contribution at `eCNinePZero` is strictly
less than `9N`. -/
theorem eCNinePZeroExplicitBranchContribution_odd_lt_nine_mul
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U) (hc : coefficient ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N) :
    eCNinePZeroExplicitBranchContribution omega Rzero s v coefficient N <
      ((9 * N : ℕ) : ℕ∞) := by
  apply (eCNinePZeroExplicitBranchContribution_odd_le
    homega hv hvCube hc hnotdiv hodd).trans_lt
  exact_mod_cast eCNine_three_mul_lt_nine_mul hnotdiv

/-- In even degree, the explicit contribution at `eCNinePZero` is strictly
less than `9N`. -/
theorem eCNinePZeroExplicitBranchContribution_even_lt_nine_mul
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {s U v : Analytic.Germ 1}
    {coefficient : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N) :
    eCNinePZeroExplicitBranchContribution omega Rzero s v coefficient N <
      ((9 * N : ℕ) : ℕ∞) := by
  apply (eCNinePZeroExplicitBranchContribution_even_le
    homega hv hvCube hvorder hc hnotdiv heven).trans_lt
  exact_mod_cast eCNine_three_mul_add_three_lt_nine_mul hnotdiv

/-- In odd degree, there are local branch data for which the explicit
contribution at `eCNinePZero` is at most `3N`. -/
theorem eCNine_exists_odd_pZero_branch_contribution_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (hodd : Odd N) :
    ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N : ℕ) : ℕ∞) := by
  obtain ⟨s, U, v, hv, hvCube, hvorder, _hinjective, _hbranches⟩ :=
    eCNine_exists_three_local_branches homega
  exact ⟨s, U, v, hv, hvCube, hvorder,
    eCNinePZeroExplicitBranchContribution_odd_le
      homega hv hvCube hc hnotdiv hodd⟩

/-- In even degree, there are local branch data for which the explicit
contribution at `eCNinePZero` is at most `3N + 3`. -/
theorem eCNine_exists_even_pZero_branch_contribution_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) (heven : Even N) :
    ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N + 3 : ℕ) : ℕ∞) := by
  obtain ⟨s, U, v, hv, hvCube, hvorder, _hinjective, _hbranches⟩ :=
    eCNine_exists_three_local_branches homega
  exact ⟨s, U, v, hv, hvCube, hvorder,
    eCNinePZeroExplicitBranchContribution_even_le
      homega hv hvCube hvorder hc hnotdiv heven⟩

/-- For every hard form, the contribution bound is `3N` in odd degree and
`3N + 3` in even degree. -/
theorem eCNine_exists_pZero_branch_contribution_le
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (Odd N ∧ ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N : ℕ) : ℕ∞)) ∨
    (Even N ∧ ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≤ ((3 * N + 3 : ℕ) : ℕ∞)) := by
  rcases Nat.even_or_odd N with heven | hodd
  · right
    exact ⟨heven, eCNine_exists_even_pZero_branch_contribution_le
      homega Rzero coefficient N hc hnotdiv heven⟩
  · left
    exact ⟨hodd, eCNine_exists_odd_pZero_branch_contribution_le
      homega Rzero coefficient N hc hnotdiv hodd⟩

/-- A noninvariant homogeneous form either gives a rotation line collision or
has the hard form together with its parity dependent local C9 bound. -/
theorem e_noninvariant_rotationLineCollision_or_pZero_branch_contribution
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hnoninvariant : R ≠ eRotateForm omega R) :
    Nonempty (ERotationLineCollisionCertificate omega R) ∨
    ∃ Rzero : ESourceRing ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 3 ∣ N ∧
      R = eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N ∧
      ((Odd N ∧ ∃ s U v : Analytic.Germ 1,
        Analytic.Germ.valueRingHom 1 v = 1 ∧
        v ^ 3 = U ∧
        Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
        eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N ≤ ((3 * N : ℕ) : ℕ∞)) ∨
      (Even N ∧ ∃ s U v : Analytic.Germ 1,
        Analytic.Germ.valueRingHom 1 v = 1 ∧
        v ^ 3 = U ∧
        Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
        eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N ≤
            ((3 * N + 3 : ℕ) : ℕ∞))) := by
  rcases e_noninvariant_rotationLineCollision_or_source_descent_add_pure_power
      homega hhomogeneous hnoninvariant with hrotation | hhard
  · exact Or.inl hrotation
  · obtain ⟨Rzero, coefficient, hc, hnotdiv, hR⟩ := hhard
    exact Or.inr ⟨Rzero, coefficient, hc, hnotdiv, hR,
      eCNine_exists_pZero_branch_contribution_le
        homega Rzero coefficient N hc hnotdiv⟩

end Germ
end OnLeConjecture.DThree
