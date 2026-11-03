/-
Copyright (c) 2026 The Tau Ceti contributors and Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullComplex
public import Mathlib.Algebra.DirectSum.Module

/-!
# The Maslov-graded full polynomial grid complex

A monomial state has degree `M_O(x) - 2 |e|`. The homogeneous pieces are
defined by the actual polynomial supports. Every empty rectangle lowers
this degree by one, including rectangles containing X markings. Restricting
the full differential to these pieces gives a chain complex indexed by ℤ.
Its square-zero identity is the proved full rectangle cancellation.

The support and restriction arguments are adapted from TauCeti at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`:
https://github.com/TauCetiProject/TauCeti/blob/eb4dd2412a1cd62f73128361bfd3cb422df32e37/TauCeti/KnotTheory/Grid/Grading/Unblocked/Chain.lean
https://github.com/TauCetiProject/TauCeti/blob/eb4dd2412a1cd62f73128361bfd3cb422df32e37/TauCeti/KnotTheory/Grid/Grading/Unblocked/Complex.lean
The original arguments concern the X-avoiding differential with two gradings.
Here only Maslov degree is used, for the full differential and every grid diagram.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory MvPolynomial

variable {n : ℕ} (G : GridDiagram n)

/-- The Maslov degree of an O-variable monomial times a grid state. -/
def maslovDegree (e : Fin n →₀ ℕ) (x : GridState n) : ℤ :=
  G.maslovOℤ x - 2 * (exponentSize e : ℤ)

@[simp]
theorem maslovDegree_zero (x : GridState n) :
    maslovDegree G 0 x = G.maslovOℤ x := by
  simp [maslovDegree]

/-- Multiplying by a monomial lowers degree by twice its total exponent. -/
theorem maslovDegree_add (d e : Fin n →₀ ℕ) (x : GridState n) :
    maslovDegree G (d + e) x = maslovDegree G e x - 2 * (exponentSize d : ℤ) := by
  simp only [maslovDegree, exponentSize_add, Nat.cast_add]
  ring

/-- The O-weighted term of every empty rectangle has degree one less than its input. -/
theorem maslovDegree_add_oExponent {x y : GridState n} (r : GridRectangleBetween x y)
    (hr : r.IsEmpty) (e : Fin n →₀ ℕ) :
    maslovDegree G (e + oExponent G r.toGridRectangle) y = maslovDegree G e x - 1 := by
  have h := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  rw [G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  have hi : G.maslovOℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) =
      G.maslovOℤ x - 1 := by exact_mod_cast h
  simp only [maslovDegree, exponentSize_add, exponentSize_oExponent, Nat.cast_add]
  omega

/-- Chains whose polynomial monomials have Maslov degrees in a prescribed set. -/
def maslovSupported (R : Type*) [CommSemiring R] (S : Set ℤ) :
    Submodule R (GridChainMinus R n) where
  carrier := {c | ∀ x : GridState n, ∀ e ∈ (c x).support, maslovDegree G e x ∈ S}
  add_mem' {a b} ha hb x e he := by
    classical
    rw [Finsupp.add_apply] at he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact ha x e h
    · exact hb x e h
  zero_mem' x e he := by simp at he
  smul_mem' a b hb x e he := by
    rw [Finsupp.smul_apply] at he
    exact hb x e (MvPolynomial.support_smul he)

private theorem maslovSupported_mono {R : Type*} [CommSemiring R] {S T : Set ℤ}
    (h : S ⊆ T) : maslovSupported G R S ≤ maslovSupported G R T :=
  fun _ hc x e he => h (hc x e he)

/-- The degree-m homogeneous chains, as a submodule over the coefficient ring. -/
def maslovPiece (R : Type*) [CommSemiring R] (m : ℤ) :
    Submodule R (GridChainMinus R n) := maslovSupported G R {m}

@[simp]
theorem mem_maslovPiece {R : Type*} [CommSemiring R] {m : ℤ} {c : GridChainMinus R n} :
    c ∈ maslovPiece G R m ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, maslovDegree G e x = m := Iff.rfl

/-- Every polynomial monomial state lies in its specified homogeneous piece. -/
theorem single_monomial_mem_maslovPiece (R : Type*) [CommSemiring R]
    (e : Fin n →₀ ℕ) (x : GridState n) (a : R) :
    (Finsupp.single x (monomial e a) : GridChainMinus R n) ∈
      maslovPiece G R (maslovDegree G e x) := by
  rw [mem_maslovPiece]
  intro z f hf
  rcases eq_or_ne z x with rfl | hzx
  · rw [Finsupp.single_eq_same] at hf
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)]
  · rw [Finsupp.single_eq_of_ne hzx] at hf
    simp at hf

theorem monomialGenerator_mem_maslovPiece (R : Type*) [CommSemiring R]
    (e : Fin n →₀ ℕ) (x : GridState n) :
    monomialGenerator R e x ∈ maslovPiece G R (maslovDegree G e x) :=
  single_monomial_mem_maslovPiece G R e x 1

/-- The full differential sends degree m to degree m-1. -/
theorem differential_mem_maslovPiece {R : Type*} [CommSemiring R]
    {m : ℤ} {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    differential G R c ∈ maslovPiece G R (m - 1) := by
  classical
  intro z f hf
  rw [differential_apply_apply, Finsupp.sum] at hf
  obtain ⟨w, -, hfw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hfw)
  obtain ⟨r, hr, hrd⟩ := G.exists_mem_of_mem_support_sum_OMonomial R hd
  change d = oExponent G r.toGridRectangle at hrd
  rw [hrd, maslovDegree_add_oExponent G r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr)]
  exact congrArg (fun k : ℤ => k - 1) (hc w e he)

/-- Scalar monomials shift the actual homogeneous pieces by their Maslov weight. -/
theorem monomial_smul_mem_maslovPiece {R : Type*} [CommSemiring R]
    (d : Fin n →₀ ℕ) (a : R) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ maslovPiece G R m) :
    (monomial d a : MvPolynomial (Fin n) R) • c ∈
      maslovPiece G R (m - 2 * (exponentSize d : ℤ)) := by
  classical
  intro z f hf
  rw [Finsupp.smul_apply, smul_eq_mul] at hf
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hf)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb), maslovDegree_add]
  exact congrArg (fun k : ℤ => k - 2 * (exponentSize d : ℤ)) (hc z e he)

/-- Every polynomial grid chain is a finite sum of homogeneous chains. -/
theorem iSup_maslovPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ m : ℤ, maslovPiece G R m = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add x p c _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    have hp : (Finsupp.single x p : GridChainMinus R n) =
        ∑ e ∈ p.support, Finsupp.single x (monomial e (p.coeff e)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      exact map_sum (Finsupp.singleAddHom x) _ _
    rw [hp]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.mem_iSup_of_mem (maslovDegree G e x)
        (single_monomial_mem_maslovPiece G R e x _)

/-- Distinct Maslov degrees give independent homogeneous submodules. -/
theorem iSupIndep_maslovPiece (R : Type*) [CommSemiring R] :
    iSupIndep (maslovPiece G R) := by
  intro m
  rw [Submodule.disjoint_def]
  intro c hc hc'
  have hcompl : c ∈ maslovSupported G R {m}ᶜ :=
    iSup₂_le (fun _ hm => maslovSupported_mono G
      (Set.singleton_subset_iff.mpr hm)) hc'
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he => hcompl z e he (hc z e he)

/-- The polynomial grid module is the internal direct sum of its Maslov pieces. -/
theorem isInternal_maslovPiece (R : Type*) [CommRing R] :
    DirectSum.IsInternal (maslovPiece G R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_maslovPiece G R) (iSup_maslovPiece_eq_top G R)

/-- The full differential restricted from degree m+1 to degree m. -/
noncomputable def gradedDifferential (R : Type*) [CommSemiring R] (m : ℤ) :
    maslovPiece G R (m + 1) →ₗ[R] maslovPiece G R m :=
  ((differential G R).restrictScalars R).restrict fun _ hc => by
    simpa using differential_mem_maslovPiece G hc

@[simp]
theorem coe_gradedDifferential (R : Type*) [CommSemiring R] (m : ℤ)
    (c : maslovPiece G R (m + 1)) :
    (gradedDifferential G R m c : GridChainMinus R n) = differential G R c := rfl

/-- Consecutive restricted differentials square to zero by full rectangle cancellation. -/
theorem gradedDifferential_comp_eq_zero (R : Type*) [CommSemiring R] [CharP R 2] (m : ℤ) :
    (gradedDifferential G R m).comp (gradedDifferential G R (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, coe_gradedDifferential,
    ZeroMemClass.coe_zero]
  exact differential_sq_eq_zero G R c

/-- The genuine integer-graded full polynomial grid complex in characteristic two. -/
noncomputable def maslovComplex (R : Type*) [CommRing R] [CharP R 2] :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (maslovPiece G R m))
    (fun m => ModuleCat.ofHom (gradedDifferential G R m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, gradedDifferential_comp_eq_zero, ModuleCat.ofHom_zero])

@[simp]
theorem maslovComplex_X (R : Type*) [CommRing R] [CharP R 2] (m : ℤ) :
    (maslovComplex G R).X m = ModuleCat.of R (maslovPiece G R m) := rfl

@[simp]
theorem maslovComplex_d (R : Type*) [CommRing R] [CharP R 2] (m : ℤ) :
    (maslovComplex G R).d (m + 1) m =
      eqToHom (maslovComplex_X G R (m + 1)) ≫
        ModuleCat.ofHom (gradedDifferential G R m) ≫
          eqToHom (maslovComplex_X G R m).symm := by
  simp only [maslovComplex, ChainComplex.of_d]
  ext c
  rfl

end OnLeConjecture.KnotFloer.GridFull
