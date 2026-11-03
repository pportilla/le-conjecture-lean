/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurent

/-!
# Integer Maslov grading of the Laurent full grid complex

The monomial `T k` times a state x has degree `M_O(x) - 2 k`, for every
integer k. The homogeneous pieces form an internal direct sum over the
coefficient ring. The full rectangle differential lowers degree by one.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n)

/-- Maslov degree of a Laurent monomial state. -/
def laurentMaslovDegree (k : ℤ) (x : GridState n) : ℤ := G.maslovOℤ x - 2 * k

@[simp]
theorem laurentMaslovDegree_zero (x : GridState n) :
    laurentMaslovDegree G 0 x = G.maslovOℤ x := by simp [laurentMaslovDegree]

theorem laurentMaslovDegree_add (j k : ℤ) (x : GridState n) :
    laurentMaslovDegree G (j + k) x = laurentMaslovDegree G k x - 2 * j := by
  simp only [laurentMaslovDegree]
  ring

/-- Empty rectangles lower the weighted Maslov degree by one. -/
theorem laurentMaslovDegree_add_card_OColumns {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) (k : ℤ) :
    laurentMaslovDegree G (k + ((G.OColumns r.toGridRectangle).card : ℤ)) y =
      laurentMaslovDegree G k x - 1 := by
  have h := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  rw [G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  have hi : G.maslovOℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) =
      G.maslovOℤ x - 1 := by exact_mod_cast h
  simp only [laurentMaslovDegree]
  omega

/-- Laurent chains whose support has Maslov degree in a specified set. -/
def laurentMaslovSupported (R : Type*) [CommSemiring R] (S : Set ℤ) :
    Submodule R (LaurentChain R n) where
  carrier := {c | ∀ x : GridState n, ∀ k ∈ (c x).coeff.support, laurentMaslovDegree G k x ∈ S}
  add_mem' {a b} ha hb x k hk := by
    classical
    rw [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] at hk
    rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
    · exact ha x k h
    · exact hb x k h
  zero_mem' x k hk := by simp at hk
  smul_mem' a b hb x k hk := by
    rw [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul] at hk
    exact hb x k (Finsupp.support_smul hk)

private theorem laurentMaslovSupported_mono {R : Type*} [CommSemiring R] {S T : Set ℤ}
    (h : S ⊆ T) : laurentMaslovSupported G R S ≤ laurentMaslovSupported G R T :=
  fun _ hc x k hk => h (hc x k hk)

/-- The degree-m part of the Laurent grid module over its coefficient ring. -/
def laurentMaslovPiece (R : Type*) [CommSemiring R] (m : ℤ) :
    Submodule R (LaurentChain R n) := laurentMaslovSupported G R {m}

@[simp]
theorem mem_laurentMaslovPiece {R : Type*} [CommSemiring R] {m : ℤ}
    {c : LaurentChain R n} :
    c ∈ laurentMaslovPiece G R m ↔
      ∀ x : GridState n, ∀ k ∈ (c x).coeff.support, laurentMaslovDegree G k x = m := Iff.rfl

/-- Every Laurent monomial state belongs to its stated homogeneous piece. -/
theorem single_monomial_mem_laurentMaslovPiece (R : Type*) [CommSemiring R]
    (k : ℤ) (x : GridState n) (a : R) :
    (Finsupp.single x (AddMonoidAlgebra.single k a) : LaurentChain R n) ∈
      laurentMaslovPiece G R (laurentMaslovDegree G k x) := by
  rw [mem_laurentMaslovPiece]
  intro z j hj
  rcases eq_or_ne z x with rfl | hzx
  · rw [Finsupp.single_eq_same, AddMonoidAlgebra.coeff_single] at hj
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hj)]
  · rw [Finsupp.single_eq_of_ne hzx] at hj
    simp at hj

theorem laurentMonomialGenerator_mem_laurentMaslovPiece (R : Type*) [CommSemiring R]
    (k : ℤ) (x : GridState n) :
    laurentMonomialGenerator R k x ∈ laurentMaslovPiece G R (laurentMaslovDegree G k x) :=
  single_monomial_mem_laurentMaslovPiece G R k x 1

/-- The full Laurent differential lowers Maslov degree by one. -/
theorem laurentDifferential_mem_maslovPiece {R : Type*} [CommSemiring R]
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    laurentDifferential G R c ∈ laurentMaslovPiece G R (m - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, hr, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentDifferential G R c hk
  rw [laurentMaslovDegree_add_card_OColumns G r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr)]
  exact congrArg (fun m : ℤ => m - 1) (hc x j hj)

/-- Multiplication by any Laurent monomial shifts degree by twice its exponent. -/
theorem laurentMonomial_smul_mem_maslovPiece {R : Type*} [CommSemiring R]
    (j : ℤ) (a : R) {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    (AddMonoidAlgebra.single j a : LaurentPolynomial R) • c ∈
      laurentMaslovPiece G R (m - 2 * j) := by
  classical
  intro y k hk
  rw [Finsupp.smul_apply, smul_eq_mul] at hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp
    (AddMonoidAlgebra.support_coeff_single_mul_subset (c y) a j hk)
  rw [laurentMaslovDegree_add]
  exact congrArg (fun m : ℤ => m - 2 * j) (hc y l hl)

/-- Every Laurent grid chain is a finite sum of homogeneous chains. -/
theorem iSup_laurentMaslovPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ m : ℤ, laurentMaslovPiece G R m = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add x p c _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    have hp : (Finsupp.single x p : LaurentChain R n) =
        ∑ k ∈ p.coeff.support, Finsupp.single x (AddMonoidAlgebra.single k (p.coeff k)) := by
      conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p, Finsupp.sum]
      exact map_sum (Finsupp.singleAddHom x) _ _
    rw [hp]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem (laurentMaslovDegree G k x)
        (single_monomial_mem_laurentMaslovPiece G R k x _)

/-- Distinct Laurent Maslov pieces are independent submodules. -/
theorem iSupIndep_laurentMaslovPiece (R : Type*) [CommSemiring R] :
    iSupIndep (laurentMaslovPiece G R) := by
  intro m
  rw [Submodule.disjoint_def]
  intro c hc hc'
  have hcompl : c ∈ laurentMaslovSupported G R {m}ᶜ :=
    iSup₂_le (fun _ hm => laurentMaslovSupported_mono G
      (Set.singleton_subset_iff.mpr hm)) hc'
  apply Finsupp.ext
  intro x
  apply LaurentPolynomial.ext
  intro k
  by_contra hk
  have hs : k ∈ (c x).coeff.support := Finsupp.mem_support_iff.mpr (by simpa using hk)
  exact hcompl x k hs (hc x k hs)

/-- The Laurent grid module is the internal direct sum of its Maslov pieces. -/
theorem isInternal_laurentMaslovPiece (R : Type*) [CommRing R] :
    DirectSum.IsInternal (laurentMaslovPiece G R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_laurentMaslovPiece G R) (iSup_laurentMaslovPiece_eq_top G R)

/-- The full Laurent differential restricted from degree m+1 to degree m. -/
noncomputable def laurentGradedDifferential (R : Type*) [CommSemiring R] (m : ℤ) :
    laurentMaslovPiece G R (m + 1) →ₗ[R] laurentMaslovPiece G R m :=
  ((laurentDifferential G R).restrictScalars R).restrict fun _ hc => by
    simpa using laurentDifferential_mem_maslovPiece G hc

@[simp]
theorem coe_laurentGradedDifferential (R : Type*) [CommSemiring R] (m : ℤ)
    (c : laurentMaslovPiece G R (m + 1)) :
    (laurentGradedDifferential G R m c : LaurentChain R n) = laurentDifferential G R c := rfl

theorem laurentGradedDifferential_comp_eq_zero (R : Type*) [CommSemiring R] [CharP R 2]
    (m : ℤ) :
    (laurentGradedDifferential G R m).comp (laurentGradedDifferential G R (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, coe_laurentGradedDifferential,
    ZeroMemClass.coe_zero]
  exact laurentDifferential_sq_eq_zero G R c

/-- The integer-graded full Laurent grid complex in characteristic two. -/
noncomputable def laurentMaslovComplex (R : Type*) [CommRing R] [CharP R 2] :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (laurentMaslovPiece G R m))
    (fun m => ModuleCat.ofHom (laurentGradedDifferential G R m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, laurentGradedDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

@[simp]
theorem laurentMaslovComplex_X (R : Type*) [CommRing R] [CharP R 2] (m : ℤ) :
    (laurentMaslovComplex G R).X m = ModuleCat.of R (laurentMaslovPiece G R m) := rfl

@[simp]
theorem laurentMaslovComplex_d (R : Type*) [CommRing R] [CharP R 2] (m : ℤ) :
    (laurentMaslovComplex G R).d (m + 1) m =
      eqToHom (laurentMaslovComplex_X G R (m + 1)) ≫
        ModuleCat.ofHom (laurentGradedDifferential G R m) ≫
          eqToHom (laurentMaslovComplex_X G R m).symm := by
  simp only [laurentMaslovComplex, ChainComplex.of_d]
  ext c
  rfl

end OnLeConjecture.KnotFloer.GridFull
