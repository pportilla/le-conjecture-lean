/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorSingleton
public import OnLeConjecture.KnotFloer.GridCanonicalSymmetry
public import OnLeConjecture.KnotFloer.GridFullCyclicFiltration

/-!
# Powers of the cyclic row translation

For every `k`, relabeling rows by `finRotate n ^ k` preserves the full Laurent
coefficients, the Maslov degrees and the Alexander gradings. The explicit
Laurent-linear row relabeling therefore induces an isomorphism of native complexes
with shifts `(0,0)` in both directions, and the isomorphism carries the normalized
class to the normalized class (M615). The case `k = 1` is the existing one-step
isomorphism `laurentMaslovCyclicRowsIso`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ}

/-- One further cyclic row step after `k` steps is `k + 1` steps. -/
theorem finRotate_pow_trans (k : ℕ) :
    ((finRotate n) ^ k).trans (finRotate n) = (finRotate n) ^ (k + 1) := by
  ext c
  simp only [Equiv.trans_apply, pow_succ', Equiv.Perm.mul_apply]

/-- Zero cyclic row steps relabel nothing. -/
theorem gridState_relabelRows_finRotate_pow_zero (x : GridState n) :
    x.relabelRows ((finRotate n) ^ 0) = x :=
  GridState.relabelRows_refl x

/-- Zero cyclic row steps relabel no marking. -/
theorem gridDiagram_relabelRows_finRotate_pow_zero (G : GridDiagram n) :
    G.relabelRows ((finRotate n) ^ 0) = G :=
  GridDiagram.relabelRows_refl G

theorem gridState_relabelRows_finRotate_pow_succ (x : GridState n) (k : ℕ) :
    x.relabelRows ((finRotate n) ^ (k + 1)) =
      (x.relabelRows ((finRotate n) ^ k)).relabelRows (finRotate n) := by
  rw [GridState.relabelRows_relabelRows, finRotate_pow_trans]

theorem gridDiagram_relabelRows_finRotate_pow_succ (G : GridDiagram n) (k : ℕ) :
    G.relabelRows ((finRotate n) ^ (k + 1)) =
      (G.relabelRows ((finRotate n) ^ k)).relabelRows (finRotate n) := by
  rw [GridDiagram.relabelRows_relabelRows, finRotate_pow_trans]

variable (G : GridDiagram n)

/-- Powers of the cyclic row translation preserve the full Laurent coefficient. -/
theorem laurentCoefficient_relabelRows_finRotate_pow (R : Type*) [CommSemiring R] (k : ℕ)
    (x y : GridState n) :
    laurentCoefficient (G.relabelRows ((finRotate n) ^ k)) R
        (x.relabelRows ((finRotate n) ^ k)) (y.relabelRows ((finRotate n) ^ k)) =
      laurentCoefficient G R x y := by
  induction k with
  | zero =>
    rw [gridDiagram_relabelRows_finRotate_pow_zero, gridState_relabelRows_finRotate_pow_zero,
      gridState_relabelRows_finRotate_pow_zero]
  | succ k ih =>
    rw [gridDiagram_relabelRows_finRotate_pow_succ, gridState_relabelRows_finRotate_pow_succ,
      gridState_relabelRows_finRotate_pow_succ, laurentCoefficient_relabelRows_finRotate, ih]

/-- Powers of the cyclic row translation preserve the integer Maslov degree. -/
theorem laurentMaslovDegree_relabelRows_finRotate_pow (k : ℕ) (j : ℤ) (x : GridState n) :
    laurentMaslovDegree (G.relabelRows ((finRotate n) ^ k)) j
        (x.relabelRows ((finRotate n) ^ k)) =
      laurentMaslovDegree G j x := by
  induction k with
  | zero =>
    rw [gridDiagram_relabelRows_finRotate_pow_zero, gridState_relabelRows_finRotate_pow_zero]
  | succ k ih =>
    rw [gridDiagram_relabelRows_finRotate_pow_succ, gridState_relabelRows_finRotate_pow_succ,
      laurentMaslovDegree_relabelRows_finRotate, ih]

/-- Powers of the cyclic row translation preserve the Alexander grading. -/
theorem alexander_relabelRows_finRotate_pow (k : ℕ) (x : GridState n) :
    (G.relabelRows ((finRotate n) ^ k)).alexander (x.relabelRows ((finRotate n) ^ k)) =
      G.alexander x := by
  induction k with
  | zero =>
    rw [gridDiagram_relabelRows_finRotate_pow_zero, gridState_relabelRows_finRotate_pow_zero]
  | succ k ih =>
    rw [gridDiagram_relabelRows_finRotate_pow_succ, gridState_relabelRows_finRotate_pow_succ,
      GridDiagram.alexander_relabelRows_finRotate, ih]

section Laurent

variable (R : Type*) [CommSemiring R] (k : ℕ)

/-- The explicit Laurent-linear equivalence translating all rows cyclically `k` times. -/
noncomputable def laurentCyclicRowsPowEquiv :
    LaurentChain R n ≃ₗ[LaurentPolynomial R] LaurentChain R n :=
  GridChain.relabelRowsEquiv ((finRotate n) ^ k)

omit G in
@[simp]
theorem laurentCyclicRowsPowEquiv_apply (c : LaurentChain R n) (x : GridState n) :
    laurentCyclicRowsPowEquiv R k c x = c (x.relabelRows ((finRotate n) ^ k).symm) :=
  GridChain.relabelRowsEquiv_apply _ _ _

/-- The `k`-fold row translation intertwines the full Laurent differentials. -/
theorem laurentDifferential_relabelRows_finRotate_pow :
    laurentDifferential (G.relabelRows ((finRotate n) ^ k)) R ∘ₗ
        (laurentCyclicRowsPowEquiv R k).toLinearMap =
      (laurentCyclicRowsPowEquiv R k).toLinearMap ∘ₗ laurentDifferential G R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelRows ((finRotate n) ^ k) = y :=
    ⟨y.relabelRows ((finRotate n) ^ k).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    laurentCyclicRowsPowEquiv, GridChain.relabelRowsEquiv_single, laurentDifferential_single,
    laurentOnGenerator_apply, GridChain.relabelRowsEquiv_apply,
    GridState.relabelRows_relabelRows, Equiv.self_trans_symm, GridState.relabelRows_refl,
    laurentCoefficient_relabelRows_finRotate_pow]

theorem laurentDifferential_relabelRows_finRotate_pow_apply (c : LaurentChain R n) :
    laurentDifferential (G.relabelRows ((finRotate n) ^ k)) R (laurentCyclicRowsPowEquiv R k c) =
      laurentCyclicRowsPowEquiv R k (laurentDifferential G R c) :=
  LinearMap.congr_fun (laurentDifferential_relabelRows_finRotate_pow G R k) c

/-- The `k`-fold row translation preserves and reflects each homogeneous submodule. -/
theorem laurentCyclicRowsPowEquiv_mem_maslovPiece_iff (m : ℤ) (c : LaurentChain R n) :
    laurentCyclicRowsPowEquiv R k c ∈
        laurentMaslovPiece (G.relabelRows ((finRotate n) ^ k)) R m ↔
      c ∈ laurentMaslovPiece G R m := by
  simp only [mem_laurentMaslovPiece]
  constructor
  · intro h x j hj
    have := h (x.relabelRows ((finRotate n) ^ k)) j
    rw [laurentMaslovDegree_relabelRows_finRotate_pow] at this
    exact this (by simpa using hj)
  · intro h y j hj
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelRows ((finRotate n) ^ k) = y :=
      ⟨y.relabelRows ((finRotate n) ^ k).symm, by simp⟩
    rw [laurentMaslovDegree_relabelRows_finRotate_pow]
    exact h x j (by simpa using hj)

end Laurent

/-- The `k`-fold row translation preserves and reflects both coefficient filtration bounds. -/
theorem laurentCyclicRowsPowEquiv_mem_bifiltrationLevel_iff (R : Type*) [CommRing R] (k : ℕ)
    (a b : ℝ) (c : LaurentChain R n) :
    laurentCyclicRowsPowEquiv R k c ∈
        laurentBifiltrationLevel (G.relabelRows ((finRotate n) ^ k)) R a b ↔
      c ∈ laurentBifiltrationLevel G R a b := by
  simp only [mem_laurentBifiltrationLevel_iff]
  constructor
  · intro h x j hj
    have := h (x.relabelRows ((finRotate n) ^ k)) j
    rw [alexander_relabelRows_finRotate_pow] at this
    exact this (by simpa using hj)
  · intro h y j hj
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelRows ((finRotate n) ^ k) = y :=
      ⟨y.relabelRows ((finRotate n) ^ k).symm, by simp⟩
    rw [alexander_relabelRows_finRotate_pow]
    exact h x j (by simpa using hj)

/-- The inverse `k`-fold row translation maps homogeneous submodules into homogeneous
submodules. -/
theorem laurentCyclicRowsPowEquiv_symm_mem_maslovPiece (R : Type*) [CommSemiring R] (k : ℕ)
    {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece (G.relabelRows ((finRotate n) ^ k)) R m) :
    (laurentCyclicRowsPowEquiv R k).symm c ∈ laurentMaslovPiece G R m :=
  (laurentCyclicRowsPowEquiv_mem_maslovPiece_iff G R k m _).mp (by
    rwa [LinearEquiv.apply_symm_apply])

/-- The inverse `k`-fold row translation intertwines the full Laurent differentials. -/
theorem laurentCyclicRowsPowEquiv_symm_differential (R : Type*) [CommSemiring R] (k : ℕ)
    (c : LaurentChain R n) :
    (laurentCyclicRowsPowEquiv R k).symm
        (laurentDifferential (G.relabelRows ((finRotate n) ^ k)) R c) =
      laurentDifferential G R ((laurentCyclicRowsPowEquiv R k).symm c) := by
  apply (laurentCyclicRowsPowEquiv R k).injective
  rw [LinearEquiv.apply_symm_apply, ← laurentDifferential_relabelRows_finRotate_pow_apply,
    LinearEquiv.apply_symm_apply]

/-- The inverse `k`-fold row translation preserves both coefficient filtration bounds. -/
theorem laurentCyclicRowsPowEquiv_symm_mem_bifiltrationLevel (R : Type*) [CommRing R] (k : ℕ)
    {a b : ℝ} {c : LaurentChain R n}
    (hc : c ∈ laurentBifiltrationLevel (G.relabelRows ((finRotate n) ^ k)) R a b) :
    (laurentCyclicRowsPowEquiv R k).symm c ∈ laurentBifiltrationLevel G R a b :=
  (laurentCyclicRowsPowEquiv_mem_bifiltrationLevel_iff G R k a b _).mp (by
    rwa [LinearEquiv.apply_symm_apply])

section Complex

variable {K : Type*} [Field K] [CharP K 2] (k : ℕ)

/-- The `k`-fold cyclic row translation is an isomorphism of native complexes. -/
def laurentMaslovCyclicRowsPowIso :
    laurentMaslovComplex G K ≅ laurentMaslovComplex (G.relabelRows ((finRotate n) ^ k)) K :=
  (laurentGridPieceData G).iso (laurentGridPieceData (G.relabelRows ((finRotate n) ^ k)))
    ((laurentCyclicRowsPowEquiv K k).restrictScalars K)
    (fun m c => laurentCyclicRowsPowEquiv_mem_maslovPiece_iff G K k m c)
    (fun c => (laurentDifferential_relabelRows_finRotate_pow_apply G K k c).symm)

/-- On underlying chains, the isomorphism is the `k`-fold row relabeling. -/
theorem laurentMaslovCyclicRowsPowIso_hom_apply (m : ℤ) (c : (laurentMaslovComplex G K).X m) :
    (laurentMaslovChainEquiv _ K m ((laurentMaslovCyclicRowsPowIso G k).hom.f m c) :
        LaurentChain K n) =
      laurentCyclicRowsPowEquiv K k (laurentMaslovChainEquiv G K m c : LaurentChain K n) :=
  PieceComplexData.iso_hom_apply _ _ _ _ _ m c

/-- On underlying chains, the inverse isomorphism is the inverse row relabeling. -/
theorem laurentMaslovCyclicRowsPowIso_inv_apply (m : ℤ)
    (c : (laurentMaslovComplex (G.relabelRows ((finRotate n) ^ k)) K).X m) :
    (laurentMaslovChainEquiv G K m ((laurentMaslovCyclicRowsPowIso G k).inv.f m c) :
        LaurentChain K n) =
      (laurentCyclicRowsPowEquiv K k).symm (laurentMaslovChainEquiv _ K m c : LaurentChain K n) :=
  PieceComplexData.iso_inv_apply _ _ _ _ _ m c

/-- The `k`-fold cyclic row isomorphism has shifts `(0,0)`. -/
theorem laurentMaslovCyclicRowsPowIso_hom_shifts :
    (laurentMaslovBifiltration G K).Shifts
      (laurentMaslovBifiltration (G.relabelRows ((finRotate n) ^ k)) K)
      (laurentMaslovCyclicRowsPowIso G k).hom 0 0 :=
  PieceComplexData.iso_hom_shifts (laurentGridPieceData G)
    (laurentGridPieceData (G.relabelRows ((finRotate n) ^ k))) _ _ _
    (fun a b c hc => (laurentCyclicRowsPowEquiv_mem_bifiltrationLevel_iff G K k a b c).mpr hc)

/-- The inverse `k`-fold cyclic row isomorphism has shifts `(0,0)`. -/
theorem laurentMaslovCyclicRowsPowIso_inv_shifts :
    (laurentMaslovBifiltration (G.relabelRows ((finRotate n) ^ k)) K).Shifts
      (laurentMaslovBifiltration G K) (laurentMaslovCyclicRowsPowIso G k).inv 0 0 :=
  PieceComplexData.iso_inv_shifts (laurentGridPieceData G)
    (laurentGridPieceData (G.relabelRows ((finRotate n) ^ k))) _ _ _
    (fun a b c hc => (laurentCyclicRowsPowEquiv_mem_bifiltrationLevel_iff G K k a b _).mp (by
      change laurentCyclicRowsPowEquiv K k ((laurentCyclicRowsPowEquiv K k).symm c) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact hc))

end Complex

/-- The `k`-fold cyclic row isomorphism carries the normalized class to the normalized class. -/
theorem gridCanonicalClass_cyclicRowsPow (hn : 2 ≤ n) (k : ℕ) :
    homologyMap (laurentMaslovCyclicRowsPowIso (K := ZMod 2) G k).hom 0
        (gridCanonicalClass G hn) =
      gridCanonicalClass (G.relabelRows ((finRotate n) ^ k)) hn :=
  gridCanonicalClass_homotopyEquiv G _ hn hn
    (HomotopyEquiv.ofIso (laurentMaslovCyclicRowsPowIso G k)) 0
    (laurentMaslovCyclicRowsPowIso_hom_shifts G k)

/-- The inverse `k`-fold cyclic row isomorphism carries the normalized class back. -/
theorem gridCanonicalClass_cyclicRowsPow_inv (hn : 2 ≤ n) (k : ℕ) :
    homologyMap (laurentMaslovCyclicRowsPowIso (K := ZMod 2) G k).inv 0
        (gridCanonicalClass (G.relabelRows ((finRotate n) ^ k)) hn) =
      gridCanonicalClass G hn :=
  gridCanonicalClass_homotopyEquiv _ G hn hn
    (HomotopyEquiv.ofIso (laurentMaslovCyclicRowsPowIso G k).symm) 0
    (laurentMaslovCyclicRowsPowIso_inv_shifts G k)

end OnLeConjecture.KnotFloer.GridFull
