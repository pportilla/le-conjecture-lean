/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariableGrading
public import OnLeConjecture.KnotFloer.GridOneVariableLaurentNormalization
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral

/-!
# The polynomial lattice in the Laurent grid module

The coefficient inclusion identifies the polynomial state module with exactly
the Laurent chains supported in nonnegative exponents. Its restriction to every
Maslov degree intertwines the full rectangle differentials.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Include every polynomial coefficient in the Laurent ring. -/
def oneVariableToLaurentChain : OneVariableChain R n →ₗ[R] LaurentChain R n :=
  Finsupp.mapRange.linearMap Polynomial.toLaurentAlg.toLinearMap

@[simp]
theorem oneVariableToLaurentChain_apply (c : OneVariableChain R n) (x : GridState n) :
    oneVariableToLaurentChain R c x = Polynomial.toLaurent (c x) := rfl

/-- The coefficient inclusion is injective. -/
theorem oneVariableToLaurentChain_injective :
    Function.Injective (oneVariableToLaurentChain R (n := n)) := by
  intro c d h
  apply Finsupp.ext
  intro x
  exact Polynomial.toLaurent_injective (DFunLike.congr_fun h x)

/-- The inclusion intertwines the full rectangle differentials. -/
theorem oneVariableToLaurentChain_differential (G : GridDiagram n) (c : OneVariableChain R n) :
    oneVariableToLaurentChain R (oneVariableDifferential R G c) =
      laurentDifferential G R (oneVariableToLaurentChain R c) := by
  classical
  apply Finsupp.ext
  intro y
  rw [oneVariableToLaurentChain_apply, oneVariableDifferential_apply_apply,
    laurentDifferential_apply_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [map_sum, map_mul, oneVariableCoefficient_toLaurent,
    oneVariableToLaurentChain_apply]

/-- Truncation recovers a Laurent polynomial whose exponents are nonnegative. -/
theorem toLaurent_trunc_of_nonneg (p : LaurentPolynomial R)
    (hp : ∀ k ∈ p.coeff.support, 0 ≤ k) :
    Polynomial.toLaurent (LaurentPolynomial.trunc p) = p := by
  have he : p = ∑ k ∈ p.coeff.support,
      LaurentPolynomial.C (p.coeff k) * LaurentPolynomial.T k := by
    simpa only [← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum] using
      (AddMonoidAlgebra.sum_coeff_single p).symm
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [LaurentPolynomial.trunc_C_mul_T, if_pos (hp k hk),
    Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg (hp k hk)]

/-- Exact characterization of the polynomial lattice by nonnegative Laurent support. -/
theorem mem_range_oneVariableToLaurentChain_iff (c : LaurentChain R n) :
    c ∈ LinearMap.range (oneVariableToLaurentChain R) ↔
      ∀ x k, k ∈ (c x).coeff.support → 0 ≤ k := by
  constructor
  · rintro ⟨p, rfl⟩ x k hk
    rw [oneVariableToLaurentChain_apply, LaurentPolynomial.support_coeff_toLaurent] at hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hk
    exact Int.natCast_nonneg j
  · intro hc
    refine ⟨Finsupp.mapRange LaurentPolynomial.trunc (map_zero _) c, ?_⟩
    apply Finsupp.ext
    intro x
    exact toLaurent_trunc_of_nonneg R (c x) (hc x)

/-- Equivalently, the first filtration coordinate of every Laurent term is at most zero. -/
theorem mem_range_oneVariableToLaurentChain_iff_firstCoordinate (c : LaurentChain R n) :
    c ∈ LinearMap.range (oneVariableToLaurentChain R) ↔
      ∀ x k, k ∈ (c x).coeff.support → -(k : ℝ) ≤ 0 := by
  rw [mem_range_oneVariableToLaurentChain_iff]
  constructor
  · intro h x k hk
    exact neg_nonpos.mpr (by exact_mod_cast h x k hk)
  · intro h x k hk
    exact_mod_cast neg_nonpos.mp (h x k hk)

/-- The coefficient inclusion preserves and reflects the exact Maslov degree. -/
theorem oneVariableToLaurentChain_mem_maslovPiece_iff (G : GridDiagram n) (a : Fin n)
    (m : ℤ) (c : OneVariableChain R n) :
    oneVariableToLaurentChain R c ∈ laurentMaslovPiece G R m ↔
      c ∈ oneVariableMaslovPiece R G a m := by
  rw [mem_laurentMaslovPiece, mem_oneVariableMaslovPiece_iff]
  constructor
  · intro h x k hk
    apply h x k
    rw [oneVariableToLaurentChain_apply, LaurentPolynomial.support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨k, hk, rfl⟩
  · intro h x k hk
    rw [oneVariableToLaurentChain_apply, LaurentPolynomial.support_coeff_toLaurent] at hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
    exact h x j hj

/-- The coefficient inclusion on a fixed Maslov degree. -/
def polynomialLatticePieceMap (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    oneVariableMaslovPiece R G a m →ₗ[R] laurentMaslovPiece G R m :=
  (oneVariableToLaurentChain R).restrict fun c hc =>
    (oneVariableToLaurentChain_mem_maslovPiece_iff R G a m c).mpr hc

/-- The degreewise image consists exactly of homogeneous chains with nonnegative exponents. -/
theorem mem_range_polynomialLatticePieceMap_iff (G : GridDiagram n) (a : Fin n) (m : ℤ)
    (c : laurentMaslovPiece G R m) :
    c ∈ LinearMap.range (polynomialLatticePieceMap R G a m) ↔
      ∀ x k, k ∈ (c.val x).coeff.support → 0 ≤ k := by
  constructor
  · rintro ⟨p, rfl⟩
    exact (mem_range_oneVariableToLaurentChain_iff R _).mp ⟨p.val, rfl⟩
  · intro hc
    obtain ⟨p, hp⟩ := (mem_range_oneVariableToLaurentChain_iff R c.val).mpr hc
    refine ⟨⟨p, (oneVariableToLaurentChain_mem_maslovPiece_iff R G a m p).mp ?_⟩, ?_⟩
    · rw [hp]
      exact c.property
    · exact Subtype.ext hp

end OnLeConjecture.KnotFloer.GridFull
