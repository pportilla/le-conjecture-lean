/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import OnLeConjecture.DThree.ECNineGenericAlgebra

/-!
# The generic C9 Kummer field

The valuation vectors established in `ECNineKummerOrders` imply that the
second Kummer function remains outside the subgroup of cubes after adjoining
a cube root of the first function.

The proof uses a primitive cube root of unity.  The associated automorphism
of the first cubic extension acts diagonally on its power basis.  Any element
whose cube lies in the base field belongs to one of the three eigenspaces.
The independence of the two Kummer classes rules out each possible
eigenspace for a cube root of the second function.
-/

public section

noncomputable section

open Polynomial Module

namespace OnLeConjecture.DThree

namespace CubicKummer

variable {K : Type*} [Field K]

abbrev P (f : K) : K[X] := X ^ 3 - C f

abbrev A (f : K) := AdjoinRoot (P f)

theorem P_monic (f : K) : (P f).Monic := by
  exact monic_X_pow_sub_C _ (by norm_num)

theorem P_natDegree (f : K) : (P f).natDegree = 3 := by
  simp [P]

variable (f : K) [Fact (Irreducible (P f))]

/-- The power basis of a cubic Kummer extension, indexed by `Fin 3`. -/
@[expose]
def basis : Basis (Fin 3) K (A f) :=
  (AdjoinRoot.powerBasis' (P_monic f)).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact P_natDegree f))

theorem basis_apply (i : Fin 3) :
    basis f i = AdjoinRoot.root (P f) ^ (i : ℕ) := by
  rw [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast, AdjoinRoot.powerBasis'_gen]

variable {omega : K} (homega : IsPrimitiveRoot omega 3)

/-- The automorphism that multiplies the cubic root by `omega`. -/
@[expose]
def sigma : A f ≃ₐ[K] A f :=
  (autAdjoinRootXPowSubC 3 f) homega.toRootsOfUnity

theorem sigma_root :
    sigma f homega (AdjoinRoot.root (P f)) =
      algebraMap K (A f) omega * AdjoinRoot.root (P f) := by
  simpa [sigma, P, Algebra.smul_def] using
    autAdjoinRootXPowSubC_root f homega.toRootsOfUnity

theorem sigma_basis (i : Fin 3) :
    sigma f homega (basis f i) =
      omega ^ (i : ℕ) • basis f i := by
  rw [basis_apply, map_pow, sigma_root, mul_pow,
    ← map_pow, ← Algebra.smul_def]

theorem basis_repr_sigma (z : A f) (i : Fin 3) :
    (basis f).repr (sigma f homega z) i =
      omega ^ (i : ℕ) * (basis f).repr z i := by
  classical
  conv_lhs => rw [← (basis f).sum_repr z]
  simp_rw [map_sum, map_smul, sigma_basis]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro c _ hci
    rw [Finsupp.single_eq_of_ne (Ne.symm hci)]
  · simp

/-- An eigenvector of the cubic root automorphism lies on the corresponding
power basis line. -/
theorem eq_smul_basis_of_sigma_eq
    (z : A f) (n : ℕ) (hn : n < 3)
    (heigen : sigma f homega z = omega ^ n • z) :
    ∃ a : K, z = a • basis f ⟨n, hn⟩ := by
  classical
  let i : Fin 3 := ⟨n, hn⟩
  refine ⟨(basis f).repr z i, ?_⟩
  apply (basis f).repr.injective
  ext j
  by_cases hji : j = i
  · subst j
    simp [i]
  · have hcoord := congrArg
      (fun y : A f ↦ (basis f).repr y j) heigen
    rw [basis_repr_sigma] at hcoord
    simp only [map_smul, Finsupp.smul_apply] at hcoord
    have hcoeff : (basis f).repr z j = 0 := by
      by_contra hne
      have hpows : omega ^ (j : ℕ) = omega ^ n :=
        mul_right_cancel₀ hne hcoord
      have hvals : (j : ℕ) = n :=
        homega.pow_inj j.isLt hn hpows
      exact hji (Fin.ext hvals)
    rw [hcoeff]
    simp only [map_smul, Basis.repr_self]
    change 0 = (basis f).repr z i * (Finsupp.single i 1 j)
    rw [Finsupp.single_eq_of_ne hji, mul_zero]

/-- If the cube of an element of a cubic Kummer extension is a nonzero
element of the base field, that element is a scalar multiple of one power of
the adjoined root. -/
theorem exists_smul_root_pow_of_cube_eq_base
    (homega : IsPrimitiveRoot omega 3)
    {g : K} (hg : g ≠ 0)
    (z : A f) (hzCube : z ^ 3 = algebraMap K (A f) g) :
    ∃ n < 3, ∃ a : K,
      z = a • AdjoinRoot.root (P f) ^ n := by
  have hmapg : algebraMap K (A f) g ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K (A f))).mpr hg
  have hz : z ≠ 0 := by
    intro hz
    apply hmapg
    rw [← hzCube, hz, zero_pow (by norm_num)]
  have hratio : (sigma f homega z / z) ^ 3 = 1 := by
    rw [div_pow, ← map_pow, hzCube, (sigma f homega).commutes,
      div_self hmapg]
  have homegaA : IsPrimitiveRoot (algebraMap K (A f) omega) 3 :=
    homega.map_of_injective (algebraMap K (A f)).injective
  obtain ⟨n, hn, hnroot⟩ := homegaA.eq_pow_of_pow_eq_one hratio
  have heigen : sigma f homega z = omega ^ n • z := by
    rw [Algebra.smul_def, map_pow]
    calc
      sigma f homega z = (sigma f homega z / z) * z :=
        (div_mul_cancel₀ _ hz).symm
      _ = (algebraMap K (A f) omega) ^ n * z := by
        rw [hnroot]
  obtain ⟨a, ha⟩ :=
    eq_smul_basis_of_sigma_eq f homega z n hn heigen
  exact ⟨n, hn, a, by simpa [basis_apply] using ha⟩

theorem cube_smul_root_pow (a : K) (n : ℕ) :
    (a • AdjoinRoot.root (P f) ^ n : A f) ^ 3 =
      algebraMap K (A f) (a ^ 3 * f ^ n) := by
  rw [Algebra.smul_def, mul_pow]
  simp only [map_pow, map_mul]
  congr 1
  rw [← pow_mul, Nat.mul_comm, pow_mul,
    root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]

/-- Independence of two Kummer classes over the base field implies that the
second class does not become a cube after adjoining a cube root of the first
class. -/
theorem not_cube_in_adjoinRoot_of_independent
    (homega : IsPrimitiveRoot omega 3) {g : K} (hg : g ≠ 0)
    (hind : ∀ {i j : ℕ}, i < 3 → j < 3 →
      ((∃ z : K, z ^ 3 = f ^ i * g ^ j) ↔ i = 0 ∧ j = 0)) :
    ∀ z : A f, z ^ 3 ≠ algebraMap K (A f) g := by
  intro z hzCube
  obtain ⟨n, hn, a, ha⟩ :=
    exists_smul_root_pow_of_cube_eq_base f homega hg z hzCube
  have hbase : a ^ 3 * f ^ n = g := by
    apply (algebraMap K (A f)).injective
    rw [← cube_smul_root_pow f a n, ← ha, hzCube]
  interval_cases n
  · have hex : ∃ x : K, x ^ 3 = f ^ 0 * g ^ 1 := by
      exact ⟨a, by simpa using hbase⟩
    have hfalse :=
      (hind (i := 0) (j := 1) (by norm_num) (by norm_num)).mp hex
    norm_num at hfalse
  · have hex : ∃ x : K, x ^ 3 = f ^ 2 * g ^ 1 := by
      refine ⟨a * f, ?_⟩
      norm_num at hbase ⊢
      rw [← hbase]
      ring
    have hfalse :=
      (hind (i := 2) (j := 1) (by norm_num) (by norm_num)).mp hex
    norm_num at hfalse
  · have hex : ∃ x : K, x ^ 3 = f ^ 1 * g ^ 1 := by
      refine ⟨a * f, ?_⟩
      norm_num at hbase ⊢
      rw [← hbase]
      ring
    have hfalse :=
      (hind (i := 1) (j := 1) (by norm_num) (by norm_num)).mp hex
    norm_num at hfalse

end CubicKummer

/-- The second Kummer function remains outside the subgroup of cubes after
adjoining a cube root of the first Kummer function. -/
theorem eCNineSecondKummerFunction_not_cube_over_first :
    ∀ z : ECNineFirstKummerAlgebra,
      z ^ 3 ≠ algebraMap ECNineKummerBase ECNineFirstKummerAlgebra
        eCNineSecondKummerFunction := by
  let omega : ECNineKummerBase := algebraMap ℂ ECNineKummerBase
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3))
  have homega : IsPrimitiveRoot omega 3 :=
    (Complex.isPrimitiveRoot_exp 3 (by norm_num)).map_of_injective
      (algebraMap ℂ ECNineKummerBase).injective
  let _ : Fact (Irreducible
      (CubicKummer.P eCNineFirstKummerFunction)) := ⟨by
    simpa [CubicKummer.P, eCNineFirstKummerPolynomial] using
      eCNineFirstKummerPolynomial_irreducible⟩
  exact CubicKummer.not_cube_in_adjoinRoot_of_independent
    eCNineFirstKummerFunction homega eCNineSecondKummerFunction_ne_zero
    (fun hi hj ↦ eCNineKummerFunctions_independent_mod_cubes hi hj)

/-- The second Kummer cubic is irreducible over the first cubic field. -/
theorem eCNineSecondKummerPolynomialOverFirst_irreducible :
    Irreducible eCNineSecondKummerPolynomialOverFirst := by
  rw [eCNineSecondKummerPolynomialOverFirst]
  exact X_pow_sub_C_irreducible_of_prime (by decide)
    eCNineSecondKummerFunction_not_cube_over_first

noncomputable instance eCNineSecondKummerPolynomialOverFirstFact :
    Fact (Irreducible eCNineSecondKummerPolynomialOverFirst) :=
  ⟨eCNineSecondKummerPolynomialOverFirst_irreducible⟩

/-- The iterated generic Kummer algebra is a field. -/
noncomputable instance eCNineKummerAlgebraField :
    Field ECNineKummerAlgebra := inferInstance

/-- The generic C9 Kummer algebra is a domain. -/
theorem eCNineKummerAlgebra_isDomain : IsDomain ECNineKummerAlgebra :=
  inferInstance

/-- The generic C9 field extension is separable. -/
theorem eCNineKummerAlgebra_isSeparable :
    Algebra.IsSeparable ECNineKummerBase ECNineKummerAlgebra :=
  inferInstance

end OnLeConjecture.DThree
