/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineAffineNormSupport
public import OnLeConjecture.DThree.ECNineBoundaryReciprocity
public import OnLeConjecture.DThree.ECNineLocalNormFactorization

/-!
# Collisions from the projective C9 norm count

The global norm count has total multiplicity `9N`. If the multiplicity at
`X = 1` is smaller than `9N`, either another finite root occurs or the
complementary chart contributes a root. Once a complementary root is known
to give the finite root `X = 0`, both alternatives yield a C9 collision away
from the distinguished point.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- If the multiplicity at `a` is smaller than the number of roots, counted
with multiplicity, then the polynomial has a root different from `a`. -/
theorem exists_isRoot_ne_of_rootMultiplicity_lt_roots_card
    {p : ℂ[X]} {a : ℂ} (hp : p ≠ 0)
    (hcard : p.rootMultiplicity a < p.roots.card) :
    ∃ z : ℂ, p.IsRoot z ∧ z ≠ a := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ z ∈ p.roots, a = z := by
    intro z hz
    exact (hnone z ((p.mem_roots hp).mp hz)).symm
  have hcount : p.roots.count a = p.roots.card :=
    Multiset.count_eq_card.mpr hall
  rw [p.count_roots] at hcount
  omega

/-- Equality of the two chart norm values at zero turns a complementary
origin root into a unit chart root at zero. -/
theorem eCNineBoundary_norm_eval_zero_gives_unit_root_zero
    {R : Form ℂ} {N : ℕ}
    (heval : (eCNineCapitalXChartDifferenceNorm R N).eval 0 =
      -(eCNineUnitDifferenceNorm R).eval 0)
    (hmultiplicity :
      (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 ≠ 0) :
    (eCNineUnitDifferenceNorm R).IsRoot 0 := by
  have hroot :
      (eCNineCapitalXChartDifferenceNorm R N).IsRoot 0 :=
    (Polynomial.rootMultiplicity_pos'.mp
      (Nat.pos_of_ne_zero hmultiplicity)).2
  rw [Polynomial.IsRoot] at hroot ⊢
  rw [heval] at hroot
  exact neg_eq_zero.mp hroot

/-- Swapping the two source pairs exchanges the two scalar C9 equations. -/
theorem eCNineEquations_swap (x t X T : ℂ) :
    ECNineEquations X T x t ↔ ECNineEquations x t X T := by
  simp only [ECNineEquations, eCNineFirstValue, eCNineSecondValue]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    constructor
    · calc
        12 * t ^ 3 + (x - X) * (X ^ 2 + 2 * X * x + 3 * x ^ 2) =
            12 * t ^ 3 - (X - x) * (3 * x ^ 2 + 2 * x * X + X ^ 2) := by
          ring
        _ = 0 := hsecond
    · calc
        12 * T ^ 3 - (x - X) * (3 * X ^ 2 + 2 * X * x + x ^ 2) =
            12 * T ^ 3 + (X - x) * (x ^ 2 + 2 * x * X + 3 * X ^ 2) := by
          ring
        _ = 0 := hfirst
  · rintro ⟨hfirst, hsecond⟩
    constructor
    · calc
        12 * T ^ 3 + (X - x) * (x ^ 2 + 2 * x * X + 3 * X ^ 2) =
            12 * T ^ 3 - (x - X) * (3 * X ^ 2 + 2 * X * x + x ^ 2) := by
          ring
        _ = 0 := hsecond
    · calc
        12 * t ^ 3 - (X - x) * (3 * x ^ 2 + 2 * x * X + X ^ 2) =
            12 * t ^ 3 + (x - X) * (X ^ 2 + 2 * X * x + 3 * x ^ 2) := by
          ring
        _ = 0 := hfirst

/-- Swapping the two source pairs negates the difference value. -/
theorem eCNineDifferenceValue_swap
    (R : Form ℂ) (x t X T : ℂ) :
    eCNineDifferenceValue R X T x t =
      -eCNineDifferenceValue R x t X T := by
  simp only [eCNineDifferenceValue]
  ring

/-- A complementary origin root gives a section zero in the chart `X = 1`
after swapping the two source pairs. -/
theorem eCNineBoundary_root_gives_swapped_initial_collision
    {R : Form ℂ} {N : ℕ}
    (heval : (eCNineCapitalXChartDifferenceNorm R N).eval 0 =
      -(eCNineUnitDifferenceNorm R).eval 0)
    (hmultiplicity :
      (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 ≠ 0) :
    ∃ t T : ℂ,
      ECNineEquations 0 t 1 T ∧
      (0, t) ≠ (1, T) ∧
      eCNineDifferenceValue R 0 t 1 T = 0 ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (0, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (1, T) := by
  have hroot : (eCNineUnitDifferenceNorm R).IsRoot 0 :=
    eCNineBoundary_norm_eval_zero_gives_unit_root_zero
      heval hmultiplicity
  obtain ⟨T, t, hequations, hsection⟩ :=
    eCNineUnitDifferenceNorm_isRoot_gives_section_zero R hroot
  have hfibre := (e_fibre_iff_C9 (one_ne_zero : (1 : ℂ) ≠ 0)).mpr
    hequations
  have hthird : MvPolynomial.eval ![(1 : ℂ), T] R =
      MvPolynomial.eval ![(0 : ℂ), t] R :=
    sub_eq_zero.mp hsection
  have hcollision :
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, T) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (0, t) := by
    funext i
    fin_cases i
    · simpa [eInvariantPolynomialMap_first] using hfibre.1
    · simpa [eInvariantPolynomialMap_second] using hfibre.2
    · exact hthird
  refine ⟨t, T, (eCNineEquations_swap 1 T 0 t).mpr hequations,
    ?_, ?_, hcollision.symm⟩
  · intro h
    have := congrArg Prod.fst h
    norm_num at this
  · rw [eCNineDifferenceValue_swap, hsection, neg_zero]

/-- The projective root count and a strict bound at `X = 1` give a finite
root away from `X = 1`, provided a complementary root supplies the finite
root `X = 0`. -/
theorem eCNineNorm_projective_count_gives_unit_root_ne_one
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hmultiplicity :
      (eCNineUnitDifferenceNorm R).rootMultiplicity 1 < 9 * N)
    (hboundary :
      (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 ≠ 0 →
        (eCNineUnitDifferenceNorm R).IsRoot 0) :
    ∃ z : ℂ,
      (eCNineUnitDifferenceNorm R).IsRoot z ∧ z ≠ 1 := by
  by_cases hboundaryMultiplicity :
      (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 = 0
  · have hcount := eCNineNorm_projective_root_count hR hnorm
    rw [hboundaryMultiplicity, add_zero] at hcount
    have hcard :
        (eCNineUnitDifferenceNorm R).rootMultiplicity 1 <
          (eCNineUnitDifferenceNorm R).roots.card := by
      rw [hcount]
      exact hmultiplicity
    obtain ⟨z, hz, hzone⟩ :=
      exists_isRoot_ne_of_rootMultiplicity_lt_roots_card hnorm hcard
    exact ⟨z, hz, hzone⟩
  · exact ⟨0, hboundary hboundaryMultiplicity, zero_ne_one⟩

/-- Under the same hypotheses, the root count gives two distinct source
points with the same value under the three initial coordinates. -/
theorem eCNineNorm_projective_count_gives_initial_collision
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hmultiplicity :
      (eCNineUnitDifferenceNorm R).rootMultiplicity 1 < 9 * N)
    (hboundary :
      (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 ≠ 0 →
        (eCNineUnitDifferenceNorm R).IsRoot 0) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (z, T) := by
  obtain ⟨z, hroot, hzone⟩ :=
    eCNineNorm_projective_count_gives_unit_root_ne_one
      hR hnorm hmultiplicity hboundary
  obtain ⟨t, T, hequations, hdistinct, hcollision⟩ :=
    eCNineUnitDifferenceNorm_isRoot_gives_initial_collision
      R hroot hzone
  exact ⟨z, t, T, hequations, hdistinct, hcollision⟩

/-- The projective root count, the strict local bound, and the equality of
the two chart norm values at zero give an initial collision. -/
theorem eCNineNorm_count_and_boundary_eval_give_initial_collision
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hmultiplicity :
      (eCNineUnitDifferenceNorm R).rootMultiplicity 1 < 9 * N)
    (heval : (eCNineCapitalXChartDifferenceNorm R N).eval 0 =
      -(eCNineUnitDifferenceNorm R).eval 0) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (z, T) := by
  apply eCNineNorm_projective_count_gives_initial_collision
    hR hnorm hmultiplicity
  intro hboundary
  exact eCNineBoundary_norm_eval_zero_gives_unit_root_zero
    heval hboundary

/-- The projective norm count and a strict local multiplicity bound give an
initial collision away from the distinguished point. -/
theorem eCNineNorm_count_gives_initial_collision
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hmultiplicity :
      (eCNineUnitDifferenceNorm R).rootMultiplicity 1 < 9 * N) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (z, T) := by
  exact eCNineNorm_count_and_boundary_eval_give_initial_collision
    hR hnorm hmultiplicity (eCNineBoundary_norm_eval_zero hR)

/-- The local norm formula and the parity bounds make the multiplicity of a
hard norm at `X = 1` strictly smaller than `9N`. -/
theorem eCNineHardNorm_rootMultiplicity_one_lt_nine_mul
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : OnLeConjecture.Analytic.Germ 1)
    (hs : OnLeConjecture.Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        OnLeConjecture.Analytic.Germ.constRingHom 1 12 *
          OnLeConjecture.Analytic.Germ.coordinate 0)
    (hrelation :
      (OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 8 * s +
            OnLeConjecture.Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : OnLeConjecture.Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder :
      OnLeConjecture.Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineUnitDifferenceNorm
        (eSourceCubeSubstitutionForm Rzero +
          MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 <
      9 * N := by
  have hformula :=
    Germ.eCNineUnitDifferenceNorm_rootMultiplicity_eq_branchContribution
      homega Rzero coefficient N s U v hs hsEquation hrelation hvCube
        hv hvorder hc hnotdiv
  have hstrict : Germ.eCNinePZeroExplicitBranchContribution
      omega Rzero s v coefficient N < ((9 * N : ℕ) : ℕ∞) := by
    rcases Nat.even_or_odd N with heven | hodd
    · exact Germ.eCNinePZeroExplicitBranchContribution_even_lt_nine_mul
        homega hv hvCube hvorder hc hnotdiv heven
    · exact Germ.eCNinePZeroExplicitBranchContribution_odd_lt_nine_mul
        homega hv hvCube hc hnotdiv hodd
  have hcast :
      (((eCNineUnitDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 : ℕ) :
          ℕ∞) < ((9 * N : ℕ) : ℕ∞) := by
    rw [hformula]
    exact hstrict
  exact_mod_cast hcast

/-- For a hard homogeneous form, the exact projective norm count and the
chart value identity at zero force an initial collision away from the
distinguished point. -/
theorem eCNineHardNorm_count_and_boundary_eval_give_initial_collision
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : OnLeConjecture.Analytic.Germ 1)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hs : OnLeConjecture.Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        OnLeConjecture.Analytic.Germ.constRingHom 1 12 *
          OnLeConjecture.Analytic.Germ.coordinate 0)
    (hrelation :
      (OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        OnLeConjecture.Analytic.Germ.constRingHom 1 6 +
          OnLeConjecture.Analytic.Germ.constRingHom 1 8 * s +
            OnLeConjecture.Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : OnLeConjecture.Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder :
      OnLeConjecture.Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (heval :
      (eCNineCapitalXChartDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N) N).eval 0 =
        -(eCNineUnitDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)).eval 0) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (1, t) =
        weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (z, T) := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  have hnorm : eCNineUnitDifferenceNorm hardForm ≠ 0 :=
    eCNineUnitDifferenceNorm_ne_zero homega hardForm Rzero coefficient N
      rfl hc hnotdiv
  have hmultiplicity :
      (eCNineUnitDifferenceNorm hardForm).rootMultiplicity 1 < 9 * N :=
    eCNineHardNorm_rootMultiplicity_one_lt_nine_mul
      homega Rzero coefficient N s U v hs hsEquation hrelation hvCube
        hv hvorder hc hnotdiv
  exact eCNineNorm_count_and_boundary_eval_give_initial_collision
    hhomogeneous hnorm hmultiplicity heval

/-- Every hard homogeneous form satisfying the chart value identity at zero
has an initial collision away from the distinguished point. -/
theorem eCNineHardNorm_boundary_eval_gives_initial_collision
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (heval :
      (eCNineCapitalXChartDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N) N).eval 0 =
        -(eCNineUnitDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)).eval 0) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (1, t) =
        weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (z, T) := by
  obtain ⟨s, U, v, hs, hsEquation, hrelation, _hU, hv, hvCube, hvorder⟩ :=
    Germ.eCNine_exists_local_branch_data
  exact eCNineHardNorm_count_and_boundary_eval_give_initial_collision
    homega Rzero coefficient N s U v hhomogeneous hs hsEquation hrelation
      hvCube hv hvorder hc hnotdiv heval

/-- Every hard homogeneous form gives an initial collision away from the
distinguished point. -/
theorem eCNineHardNorm_gives_initial_collision
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    ∃ z t T : ℂ,
      ECNineEquations 1 t z T ∧
      (1, t) ≠ (z, T) ∧
      weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (1, t) =
        weightedPolynomialMap
          (eInvariantPolynomialMap
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)) (z, T) := by
  exact eCNineHardNorm_boundary_eval_gives_initial_collision
    homega Rzero coefficient N hhomogeneous hc hnotdiv
      (eCNineBoundary_norm_eval_zero hhomogeneous)

end OnLeConjecture.DThree
