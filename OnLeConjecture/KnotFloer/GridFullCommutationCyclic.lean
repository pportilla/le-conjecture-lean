/-
Copyright (c) 2026 The Tau Ceti contributors, Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Differential.CyclicPermutation
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.CyclicPermutation

/-!
# Cyclic translation of the full Laurent grid complex

Cyclic row and column relabelings give explicit chain isomorphisms for the
full differential, including rectangles containing X markings. The rectangle
bijections, O-count identities, and grading identities are the checked
TauCeti cyclic-permutation results at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`.

The coefficient and intertwining proofs adapt
`TauCeti/KnotTheory/Grid/Differential/CyclicPermutation.lean`, using every
empty rectangle in place of the X-avoiding rectangle set. Collapsing the
O variables makes the column relabeling linear over the Laurent ring.
This file treats cyclic translations, not general adjacent commutations or
stabilization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory GridRectangleBetween

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- Cyclic row translation preserves the full Laurent coefficient. -/
@[simp]
theorem laurentCoefficient_relabelRows_finRotate (x y : GridState n) :
    laurentCoefficient (G.relabelRows (finRotate n)) R
        (x.relabelRows (finRotate n)) (y.relabelRows (finRotate n)) =
      laurentCoefficient G R x y := by
  rw [laurentCoefficient_eq, laurentCoefficient_eq]
  refine (Finset.sum_equiv (relabelRowsEquiv (finRotate n) x y) (fun r => ?_)
    (fun r _ => ?_)).symm
  · simp only [mem_emptyRectangles, isEmpty_relabelRowsEquiv_finRotate]
  · rw [G.OColumns_relabelRows_finRotate]

/-- Cyclic column translation preserves the collapsed Laurent coefficient. -/
@[simp]
theorem laurentCoefficient_relabelColumns_finRotate (x y : GridState n) :
    laurentCoefficient (G.relabelColumns (finRotate n)) R
        (x.relabelColumns (finRotate n)) (y.relabelColumns (finRotate n)) =
      laurentCoefficient G R x y := by
  rw [laurentCoefficient_eq, laurentCoefficient_eq]
  refine (Finset.sum_equiv (relabelColumnsEquiv (finRotate n) x y) (fun r => ?_)
    (fun r _ => ?_)).symm
  · simp only [mem_emptyRectangles, isEmpty_relabelColumnsEquiv_finRotate]
  · rw [G.OColumns_relabelColumns_finRotate, Finset.card_map]

/-- The explicit Laurent-linear equivalence translating all rows cyclically. -/
noncomputable def laurentCyclicRowsEquiv : LaurentChain R n ≃ₗ[LaurentPolynomial R]
    LaurentChain R n := GridChain.relabelRowsEquiv (finRotate n)

/-- The explicit Laurent-linear equivalence translating all columns cyclically. -/
noncomputable def laurentCyclicColumnsEquiv : LaurentChain R n ≃ₗ[LaurentPolynomial R]
    LaurentChain R n := GridChain.relabelColumnsEquiv (finRotate n)

@[simp]
theorem laurentCyclicRowsEquiv_apply (c : LaurentChain R n) (x : GridState n) :
    laurentCyclicRowsEquiv R c x = c (x.relabelRows (finRotate n).symm) :=
  GridChain.relabelRowsEquiv_apply _ _ _

@[simp]
theorem laurentCyclicColumnsEquiv_apply (c : LaurentChain R n) (x : GridState n) :
    laurentCyclicColumnsEquiv R c x = c (x.relabelColumns (finRotate n).symm) :=
  GridChain.relabelColumnsEquiv_apply _ _ _

/-- Row translation intertwines the actual full Laurent differentials. -/
theorem laurentDifferential_relabelRows_finRotate :
    laurentDifferential (G.relabelRows (finRotate n)) R ∘ₗ
        (laurentCyclicRowsEquiv R).toLinearMap =
      (laurentCyclicRowsEquiv R).toLinearMap ∘ₗ laurentDifferential G R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelRows (finRotate n) = y :=
    ⟨y.relabelRows (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    laurentCyclicRowsEquiv, GridChain.relabelRowsEquiv_single, laurentDifferential_single,
    laurentOnGenerator_apply, GridChain.relabelRowsEquiv_apply,
    GridState.relabelRows_relabelRows, Equiv.self_trans_symm, GridState.relabelRows_refl,
    laurentCoefficient_relabelRows_finRotate]

/-- Column translation intertwines the actual full Laurent differentials. -/
theorem laurentDifferential_relabelColumns_finRotate :
    laurentDifferential (G.relabelColumns (finRotate n)) R ∘ₗ
        (laurentCyclicColumnsEquiv R).toLinearMap =
      (laurentCyclicColumnsEquiv R).toLinearMap ∘ₗ laurentDifferential G R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelColumns (finRotate n) = y :=
    ⟨y.relabelColumns (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    laurentCyclicColumnsEquiv, GridChain.relabelColumnsEquiv_single, laurentDifferential_single,
    laurentOnGenerator_apply, GridChain.relabelColumnsEquiv_apply,
    GridState.relabelColumns_relabelColumns, Equiv.self_trans_symm, GridState.relabelColumns_refl,
    laurentCoefficient_relabelColumns_finRotate]

@[simp]
theorem laurentDifferential_relabelRows_finRotate_apply (c : LaurentChain R n) :
    laurentDifferential (G.relabelRows (finRotate n)) R (laurentCyclicRowsEquiv R c) =
      laurentCyclicRowsEquiv R (laurentDifferential G R c) :=
  LinearMap.congr_fun (laurentDifferential_relabelRows_finRotate G R) c

@[simp]
theorem laurentDifferential_relabelColumns_finRotate_apply (c : LaurentChain R n) :
    laurentDifferential (G.relabelColumns (finRotate n)) R (laurentCyclicColumnsEquiv R c) =
      laurentCyclicColumnsEquiv R (laurentDifferential G R c) :=
  LinearMap.congr_fun (laurentDifferential_relabelColumns_finRotate G R) c

omit R in
/-- The actual integer Maslov degree is preserved by cyclic row translation. -/
@[simp]
theorem laurentMaslovDegree_relabelRows_finRotate (k : ℤ) (x : GridState n) :
    laurentMaslovDegree (G.relabelRows (finRotate n)) k (x.relabelRows (finRotate n)) =
      laurentMaslovDegree G k x := by
  have h := G.maslovO_relabelRows_finRotate x
  rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast] at h
  have hi : (G.relabelRows (finRotate n)).maslovOℤ (x.relabelRows (finRotate n)) =
      G.maslovOℤ x := by exact_mod_cast h
  simp only [laurentMaslovDegree, hi]

omit R in
/-- The actual integer Maslov degree is preserved by cyclic column translation. -/
@[simp]
theorem laurentMaslovDegree_relabelColumns_finRotate (k : ℤ) (x : GridState n) :
    laurentMaslovDegree (G.relabelColumns (finRotate n)) k (x.relabelColumns (finRotate n)) =
      laurentMaslovDegree G k x := by
  have h := G.maslovO_relabelColumns_finRotate x
  rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast] at h
  have hi : (G.relabelColumns (finRotate n)).maslovOℤ (x.relabelColumns (finRotate n)) =
      G.maslovOℤ x := by exact_mod_cast h
  simp only [laurentMaslovDegree, hi]

/-- Row translation preserves and reflects each homogeneous submodule. -/
theorem laurentCyclicRowsEquiv_mem_maslovPiece_iff (m : ℤ) (c : LaurentChain R n) :
    laurentCyclicRowsEquiv R c ∈ laurentMaslovPiece (G.relabelRows (finRotate n)) R m ↔
      c ∈ laurentMaslovPiece G R m := by
  simp only [mem_laurentMaslovPiece]
  constructor
  · intro h x k hk
    have := h (x.relabelRows (finRotate n)) k
    simpa using this (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelRows (finRotate n) = y :=
      ⟨y.relabelRows (finRotate n).symm, by simp⟩
    simpa using h x k (by simpa using hk)

/-- Column translation preserves and reflects each homogeneous submodule. -/
theorem laurentCyclicColumnsEquiv_mem_maslovPiece_iff (m : ℤ) (c : LaurentChain R n) :
    laurentCyclicColumnsEquiv R c ∈ laurentMaslovPiece (G.relabelColumns (finRotate n)) R m ↔
      c ∈ laurentMaslovPiece G R m := by
  simp only [mem_laurentMaslovPiece]
  constructor
  · intro h x k hk
    have := h (x.relabelColumns (finRotate n)) k
    simpa using this (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelColumns (finRotate n) = y :=
      ⟨y.relabelColumns (finRotate n).symm, by simp⟩
    simpa using h x k (by simpa using hk)

/-- Cyclic row translation identifies the degree-m Laurent submodules. -/
noncomputable def laurentCyclicRowsPieceEquiv (m : ℤ) :
    laurentMaslovPiece G R m ≃ₗ[R] laurentMaslovPiece (G.relabelRows (finRotate n)) R m :=
  ((laurentCyclicRowsEquiv R).restrictScalars R).ofSubmodules _ _ (by
    ext c
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (laurentCyclicRowsEquiv_mem_maslovPiece_iff G R m d).mpr hd
    · intro hc
      refine ⟨(laurentCyclicRowsEquiv R).symm c, ?_,
        (laurentCyclicRowsEquiv R).apply_symm_apply c⟩
      exact (laurentCyclicRowsEquiv_mem_maslovPiece_iff G R m _).mp (by simpa using hc))

/-- Cyclic column translation identifies the degree-m Laurent submodules. -/
noncomputable def laurentCyclicColumnsPieceEquiv (m : ℤ) :
    laurentMaslovPiece G R m ≃ₗ[R] laurentMaslovPiece (G.relabelColumns (finRotate n)) R m :=
  ((laurentCyclicColumnsEquiv R).restrictScalars R).ofSubmodules _ _ (by
    ext c
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (laurentCyclicColumnsEquiv_mem_maslovPiece_iff G R m d).mpr hd
    · intro hc
      refine ⟨(laurentCyclicColumnsEquiv R).symm c, ?_,
        (laurentCyclicColumnsEquiv R).apply_symm_apply c⟩
      exact (laurentCyclicColumnsEquiv_mem_maslovPiece_iff G R m _).mp (by simpa using hc))

@[simp]
theorem coe_laurentCyclicRowsPieceEquiv (m : ℤ) (c : laurentMaslovPiece G R m) :
    (laurentCyclicRowsPieceEquiv G R m c : LaurentChain R n) = laurentCyclicRowsEquiv R c := rfl

@[simp]
theorem coe_laurentCyclicColumnsPieceEquiv (m : ℤ) (c : laurentMaslovPiece G R m) :
    (laurentCyclicColumnsPieceEquiv G R m c : LaurentChain R n) =
      laurentCyclicColumnsEquiv R c := rfl

/-- Restricted row translation commutes with the Maslov-graded differential. -/
theorem laurentGradedDifferential_cyclicRows (m : ℤ)
    (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential (G.relabelRows (finRotate n)) R m
        (laurentCyclicRowsPieceEquiv G R (m + 1) c) =
      laurentCyclicRowsPieceEquiv G R m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  simp

/-- Restricted column translation commutes with the Maslov-graded differential. -/
theorem laurentGradedDifferential_cyclicColumns (m : ℤ)
    (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential (G.relabelColumns (finRotate n)) R m
        (laurentCyclicColumnsPieceEquiv G R (m + 1) c) =
      laurentCyclicColumnsPieceEquiv G R m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  simp

/-- Cyclic row translation is an isomorphism of the full integer-graded Laurent complexes. -/
noncomputable def laurentMaslovCyclicRowsIso (S : Type*) [CommRing S] [CharP S 2] :
    laurentMaslovComplex G S ≅ laurentMaslovComplex (G.relabelRows (finRotate n)) S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (laurentCyclicRowsPieceEquiv G S m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      simp only [laurentMaslovComplex_d]
      ext c : 2
      exact laurentGradedDifferential_cyclicRows G S j c)

/-- Cyclic column translation is an isomorphism of the full integer-graded Laurent complexes. -/
noncomputable def laurentMaslovCyclicColumnsIso (S : Type*) [CommRing S] [CharP S 2] :
    laurentMaslovComplex G S ≅ laurentMaslovComplex (G.relabelColumns (finRotate n)) S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (laurentCyclicColumnsPieceEquiv G S m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      simp only [laurentMaslovComplex_d]
      ext c : 2
      exact laurentGradedDifferential_cyclicColumns G S j c)

end OnLeConjecture.KnotFloer.GridFull
