/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingIdentification
public import OnLeConjecture.KnotFloer.GridExteriorOColour

/-!
# Rectangle operators weighted by their O columns, and their matching paths

For a grid diagram `H` and a function `φ` from sets of columns to Laurent polynomials, the
operator `colRectMap H φ` counts every empty rectangle `r` with weight `φ (H.OColumns r)`. The
native Laurent differential is `colRectMap H (fun Q => T^{|Q|})`
(`laurentDifferential_eq_colRectMap`). For a set `P` of columns the colour derivative is
`colRectMap H (colourWeight P)`, where `colourWeight P Q = |P ∩ Q| T^{|Q| - 1}`
(`oDerivative_eq_colRectMap`). The colour weight satisfies the Leibniz rule
`colourWeight_union` on disjoint unions.

For the stabilization `A = G.stabilizeX s.castSucc (G.X s).castSucc s`, the file defines the four
blocks of `colRectMap A φ` with respect to the center states and the noncritical matching
sources and targets (`stabilizationWeightedEntry`, `stabilizationWeightedExit`,
`stabilizationWeightedDirect`, `stabilizationWeightedInternal`), and the internal block with its
diagonal removed (`stabilizationWeightedTransition`). For `φ = T^{|·|}` these are the blocks of
`GridStabilizationMatchingSchur`. The composites of an entry and an exit, and of an entry, a
transition and an exit, expand as sums over the two-rectangle and three-rectangle matching paths
of `GridStabilizationMatchingTwoPath` and `GridStabilizationMatchingThreePathEquiv`, with the
product of the weights of the rectangles of the path
(`stabilizationWeightedExit_entry_single_apply_eq_sum_paths`,
`stabilizationWeightedExit_transition_entry_single_apply_eq_sum_paths`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

/-! ### Colour weights -/

section Weights

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The derivative weight of a rectangle with `O` columns `Q` for the colour set `P`. -/
def colourWeight (P Q : Finset (Fin m)) : LaurentPolynomial R :=
  ((P ∩ Q).card : LaurentPolynomial R) * LaurentPolynomial.T ((Q.card : ℤ) - 1)

/-- The Leibniz rule for colour weights on a disjoint union. -/
theorem colourWeight_union (P : Finset (Fin m)) {Q₁ Q₂ : Finset (Fin m)} (h : Disjoint Q₁ Q₂) :
    colourWeight (R := R) P (Q₁ ∪ Q₂) =
      colourWeight P Q₁ * LaurentPolynomial.T (Q₂.card : ℤ) +
        LaurentPolynomial.T (Q₁.card : ℤ) * colourWeight P Q₂ := by
  have hP : Disjoint (P ∩ Q₁) (P ∩ Q₂) :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right h
  unfold colourWeight
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hP,
    Finset.card_union_of_disjoint h]
  have e1 : (LaurentPolynomial.T ((Q₁.card : ℤ) - 1) : LaurentPolynomial R) *
      LaurentPolynomial.T (Q₂.card : ℤ) =
      LaurentPolynomial.T (((Q₁.card + Q₂.card : ℕ) : ℤ) - 1) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  have e2 : (LaurentPolynomial.T (Q₁.card : ℤ) : LaurentPolynomial R) *
      LaurentPolynomial.T ((Q₂.card : ℤ) - 1) =
      LaurentPolynomial.T (((Q₁.card + Q₂.card : ℕ) : ℤ) - 1) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  calc (((P ∩ Q₁).card + (P ∩ Q₂).card : ℕ) : LaurentPolynomial R) *
        LaurentPolynomial.T (((Q₁.card + Q₂.card : ℕ) : ℤ) - 1)
      = ((P ∩ Q₁).card : LaurentPolynomial R) *
          (LaurentPolynomial.T ((Q₁.card : ℤ) - 1) * LaurentPolynomial.T (Q₂.card : ℤ)) +
        (LaurentPolynomial.T (Q₁.card : ℤ) * LaurentPolynomial.T ((Q₂.card : ℤ) - 1)) *
          ((P ∩ Q₂).card : LaurentPolynomial R) := by
        rw [e1, e2]
        push_cast
        ring
    _ = _ := by ring

/-- The colour weight of an embedded set of columns. -/
theorem colourWeight_map {k : ℕ} (e : Fin k ↪ Fin m) (P : Finset (Fin m)) (Q : Finset (Fin k)) :
    colourWeight (R := R) P (Q.map e) = colourWeight (P.preimage e e.injective.injOn) Q := by
  classical
  have h : P ∩ Q.map e = (P.preimage e e.injective.injOn ∩ Q).map e := by
    ext c
    simp only [Finset.mem_inter, Finset.mem_map, Finset.mem_preimage]
    constructor
    · rintro ⟨hc, d, hd, rfl⟩
      exact ⟨d, ⟨hc, hd⟩, rfl⟩
    · rintro ⟨d, ⟨hc, hd⟩, rfl⟩
      exact ⟨hc, d, hd, rfl⟩
  unfold colourWeight
  rw [h, Finset.card_map, Finset.card_map]

theorem colourWeight_empty (P : Finset (Fin m)) :
    colourWeight (R := R) P ∅ = 0 := by
  simp [colourWeight]

end Weights

/-! ### Rectangle operators weighted by their O columns -/

section RectangleOperators

variable {m : ℕ} (H : GridDiagram m) {R : Type*} [CommRing R]

/-- The weighted count of empty rectangles, each weighted by a function of its `O` columns. -/
def colRectCoeff (φ : Finset (Fin m) → LaurentPolynomial R) (x y : GridState m) :
    LaurentPolynomial R :=
  ∑ r ∈ GridRectangleBetween.emptyRectangles x y, φ (H.OColumns r.toGridRectangle)

/-- The operator counting empty rectangles with weights depending on their `O` columns. -/
def colRectMap (φ : Finset (Fin m) → LaurentPolynomial R) :
    Module.End (LaurentPolynomial R) (LaurentChain R m) :=
  gridMatrixMap (colRectCoeff H φ)

theorem colRectMap_single_apply (φ : Finset (Fin m) → LaurentPolynomial R) (x z : GridState m) :
    colRectMap H φ (single x 1) z = colRectCoeff H φ x z :=
  gridMatrixMap_single_apply _ x z

/-- The native Laurent differential weights every rectangle by `T^{n_O}`. -/
theorem laurentDifferential_eq_colRectMap :
    laurentDifferential H R = colRectMap H fun Q => LaurentPolynomial.T (Q.card : ℤ) := by
  apply gridLinearMap_ext
  intro x z
  rw [laurentDifferential_single, laurentOnGenerator_apply, laurentCoefficient_eq,
    colRectMap_single_apply]
  rfl

/-- The colour derivative weights every rectangle by its colour weight. -/
theorem oDerivative_eq_colRectMap (P : Finset (Fin m)) :
    oDerivative R H P = colRectMap H (colourWeight P) := by
  classical
  apply gridLinearMap_ext
  intro x z
  rw [oDerivative_eq_sum, colRectMap_single_apply, colRectCoeff, LinearMap.sum_apply,
    Finsupp.finsetSum_apply]
  simp only [oDerivative_singleton_single_apply, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hset : P.filter (fun h => (h, H.O h) ∈ r.toGridRectangle.coveredSquares) =
      P ∩ H.OColumns r.toGridRectangle := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_inter, GridDiagram.mem_OColumns]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hset,
    colourWeight]

end RectangleOperators

/-! ### The matching blocks of a weighted operator on the stabilized grid -/

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) {R : Type*} [CommRing R]

/-- The weighted operator from the center states to the noncritical matching targets. -/
def stabilizationWeightedEntry (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    LaurentChain R n →ₗ[LaurentPolynomial R]
      (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  stabilizationMatchingTargetProjection G s R ∘ₗ
    colRectMap (G.stabilizeX s.castSucc (G.X s).castSucc s) φ ∘ₗ
      laurentStabilizationCenterInclusion G s R

/-- The weighted operator from the noncritical matching sources to the center states. -/
def stabilizationWeightedExit (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R n :=
  laurentStabilizationCenterProjection G s R ∘ₗ
    colRectMap (G.stabilizeX s.castSucc (G.X s).castSucc s) φ ∘ₗ
      stabilizationMatchingSourceInclusion G s R

/-- The weighted operator between center states. -/
def stabilizationWeightedDirect (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    Module.End (LaurentPolynomial R) (LaurentChain R n) :=
  laurentStabilizationCenterProjection G s R ∘ₗ
    colRectMap (G.stabilizeX s.castSucc (G.X s).castSucc s) φ ∘ₗ
      laurentStabilizationCenterInclusion G s R

/-- The weighted operator from the noncritical matching sources to their targets. -/
def stabilizationWeightedInternal (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  stabilizationMatchingTargetProjection G s R ∘ₗ
    colRectMap (G.stabilizeX s.castSucc (G.X s).castSucc s) φ ∘ₗ
      stabilizationMatchingSourceInclusion G s R

/-- The internal weighted operator with its matching diagonal removed. -/
def stabilizationWeightedTransition (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  stabilizationWeightedInternal G s φ - φ ∅ • LinearMap.id

variable (φ : Finset (Fin (n + 1)) → LaurentPolynomial R)

theorem stabilizationWeightedEntry_single_apply (x : GridState n)
    (z : StabilizationMatchingNode G s) :
    stabilizationWeightedEntry G s φ (single x 1) z =
      colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ
        (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s z) := by
  simp only [stabilizationWeightedEntry, LinearMap.comp_apply,
    laurentStabilizationCenterInclusion_single, stabilizationMatchingTargetProjection_apply,
    colRectMap_single_apply]

theorem stabilizationWeightedExit_single_apply (z : StabilizationMatchingNode G s)
    (y : GridState n) :
    stabilizationWeightedExit G s φ (single z 1) y =
      colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ z.val
        (y.insertPoint s.succ (G.X s).succ) := by
  simp only [stabilizationWeightedExit, LinearMap.comp_apply,
    stabilizationMatchingSourceInclusion_single, laurentStabilizationCenterProjection_apply,
    colRectMap_single_apply]

theorem stabilizationWeightedDirect_single_apply (x y : GridState n) :
    stabilizationWeightedDirect G s φ (single x 1) y =
      colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) := by
  simp only [stabilizationWeightedDirect, LinearMap.comp_apply,
    laurentStabilizationCenterInclusion_single, laurentStabilizationCenterProjection_apply,
    colRectMap_single_apply]

theorem stabilizationWeightedInternal_single_apply (a b : StabilizationMatchingNode G s) :
    stabilizationWeightedInternal G s φ (single a 1) b =
      colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ a.val
        (stabilizationMatchingTargetState G s b) := by
  simp only [stabilizationWeightedInternal, LinearMap.comp_apply,
    stabilizationMatchingSourceInclusion_single, stabilizationMatchingTargetProjection_apply,
    colRectMap_single_apply]

/-- The matching diagonal of a weighted operator carries the weight of the empty column set. -/
theorem colRectCoeff_stabilizationMatching_diagonal (a : StabilizationMatchingNode G s) :
    colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ a.val
      (stabilizationMatchingTargetState G s a) = φ ∅ := by
  rw [colRectCoeff, stabilizationMatchingTargetState,
    emptyRectangles_stabilizationMatching_source G s a.val a.property.1 a.property.2,
    Finset.sum_singleton, stabilizationRowRectangle_source_OColumns G s a.val a.property.1]

open Classical in
theorem stabilizationWeightedTransition_single_apply (a b : StabilizationMatchingNode G s) :
    stabilizationWeightedTransition G s φ (single a 1) b =
      if a = b then 0 else
        colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ a.val
          (stabilizationMatchingTargetState G s b) := by
  classical
  rw [stabilizationWeightedTransition, LinearMap.sub_apply, Finsupp.sub_apply,
    stabilizationWeightedInternal_single_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one, colRectCoeff_stabilizationMatching_diagonal, sub_self]
  · rw [if_neg h, if_neg h, mul_zero, sub_zero]

/-- With a vanishing weight on the empty column set, the internal block has no diagonal. -/
theorem stabilizationWeightedTransition_eq_internal (h : φ ∅ = 0) :
    stabilizationWeightedTransition G s φ = stabilizationWeightedInternal G s φ := by
  rw [stabilizationWeightedTransition, h, zero_smul, sub_zero]

/-! ### The blocks of the native differential -/

theorem stabilizationWeightedEntry_laurent [CharP R 2] :
    stabilizationWeightedEntry G s (fun Q => LaurentPolynomial.T (Q.card : ℤ)) =
      stabilizationMatchingEntry G s R := by
  rw [stabilizationWeightedEntry, stabilizationMatchingEntry, laurentDifferential_eq_colRectMap]

theorem stabilizationWeightedExit_laurent [CharP R 2] :
    stabilizationWeightedExit G s (fun Q => LaurentPolynomial.T (Q.card : ℤ)) =
      stabilizationMatchingExit G s R := by
  rw [stabilizationWeightedExit, stabilizationMatchingExit, laurentDifferential_eq_colRectMap]

theorem stabilizationWeightedTransition_laurent [CharP R 2] :
    stabilizationWeightedTransition G s (fun Q => LaurentPolynomial.T (Q.card : ℤ)) =
      stabilizationMatchingTransition G s R := by
  rw [stabilizationWeightedTransition, stabilizationWeightedInternal,
    ← laurentDifferential_eq_colRectMap, Finset.card_empty, Nat.cast_zero,
    LaurentPolynomial.T_zero, one_smul]
  rfl

/-! ### Two-rectangle matching paths -/

set_option backward.isDefEq.respectTransparency false in
/-- An entry followed by an exit counts every two-rectangle matching path with the product of
its two weights. -/
theorem stabilizationWeightedExit_entry_single_apply_eq_sum_paths
    (φ₁ φ₂ : Finset (Fin (n + 1)) → LaurentPolynomial R) (x y : GridState n) :
    stabilizationWeightedExit G s φ₂ (stabilizationWeightedEntry G s φ₁ (single x 1)) y =
      ∑ p ∈ stabilizationMatchingTwoPaths G s x y,
        φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns p.2.1.val.toGridRectangle) *
          φ₂ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.val.toGridRectangle) := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  let E (z : StabilizationMatchingNode G s) :=
    { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationMatchingTargetState G s z) // e.IsEmpty }
  let F (z : StabilizationMatchingNode G s) :=
    { f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }
  let (z : StabilizationMatchingNode G s) : Fintype (E z) := Fintype.ofFinite _
  let (z : StabilizationMatchingNode G s) : Fintype (F z) := Fintype.ofFinite _
  have huniv : stabilizationMatchingTwoPaths G s x y =
      Finset.univ.sigma (fun z : StabilizationMatchingNode G s =>
        (Finset.univ : Finset (E z)).product (Finset.univ : Finset (F z))) := by
    ext p
    constructor
    · intro _
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
    · intro _
      exact mem_stabilizationMatchingTwoPaths G s p
  rw [laurentMap_apply_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), huniv,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  rw [stabilizationWeightedEntry_single_apply, stabilizationWeightedExit_single_apply,
    colRectCoeff, colRectCoeff,
    Finset.sum_subtype _ (fun e => GridRectangleBetween.mem_emptyRectangles e),
    Finset.sum_subtype _ (fun f => GridRectangleBetween.mem_emptyRectangles f)]
  · let a (e : E z) : LaurentPolynomial R :=
      φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle)
    let b (f : F z) : LaurentPolynomial R :=
      φ₂ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle)
    change (∑ e, a e) * (∑ f, b f) =
      ∑ p ∈ (Finset.univ : Finset (E z)).product (Finset.univ : Finset (F z)), a p.1 * b p.2
    exact (Finset.sum_mul_sum Finset.univ Finset.univ a b).trans
      (Finset.sum_product Finset.univ Finset.univ (fun p => a p.1 * b p.2)).symm

/-! ### Three-rectangle matching paths -/

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem stabilizationWeightedExit_transition_entry_single_apply_eq_sum_nodes
    (φ₁ φ₂ φ₃ : Finset (Fin (n + 1)) → LaurentPolynomial R) (x y : GridState n) :
    letI := Fintype.ofFinite (StabilizationMatchingNode G s)
    stabilizationWeightedExit G s φ₃
        (stabilizationWeightedTransition G s φ₂
          (stabilizationWeightedEntry G s φ₁ (single x 1))) y =
      ∑ a : StabilizationMatchingNode G s, ∑ b : StabilizationMatchingNode G s,
        colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ₁
            (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s a) *
          (if a = b then 0 else
            colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ₂
              a.val (stabilizationMatchingTargetState G s b)) *
          colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ₃
            b.val (y.insertPoint s.succ (G.X s).succ) := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  rw [laurentMap_apply_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  have ht (b : StabilizationMatchingNode G s) :
      stabilizationWeightedTransition G s φ₂ (stabilizationWeightedEntry G s φ₁ (single x 1)) b =
        ∑ a : StabilizationMatchingNode G s,
          stabilizationWeightedEntry G s φ₁ (single x 1) a *
            stabilizationWeightedTransition G s φ₂ (single a 1) b :=
    finiteEnd_apply_apply _ _ _
  simp_rw [ht, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [stabilizationWeightedEntry_single_apply,
    stabilizationWeightedTransition_single_apply, stabilizationWeightedExit_single_apply]

private theorem mul_sum_mul_sum' {A B : Type*} [Fintype A] [Fintype B]
    (c : LaurentPolynomial R) (f : A → LaurentPolynomial R) (g : B → LaurentPolynomial R) :
    c * (∑ a, f a) * (∑ b, g b) =
      ∑ p ∈ (Finset.univ : Finset A).product (Finset.univ : Finset B), c * f p.1 * g p.2 := by
  have h : c * (∑ a, f a) = ∑ a, c * f a := Finset.mul_sum _ _ _
  rw [h]
  exact (Finset.sum_mul_sum Finset.univ Finset.univ (fun a => c * f a) g).trans
    (Finset.sum_product Finset.univ Finset.univ (fun p => c * f p.1 * g p.2)).symm

private theorem colRectCoeff_eq_advancing_sum (φ : Finset (Fin (n + 1)) → LaurentPolynomial R)
    {x : GridState n} (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    [Fintype { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
      m.IsEmpty ∧ m.top = (G.X s).castSucc }] :
    colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ
        a.val (stabilizationMatchingTargetState G s b) =
      ∑ m : { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
          m.IsEmpty ∧ m.top = (G.X s).castSucc },
        φ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns m.val.toGridRectangle) := by
  classical
  rw [colRectCoeff]
  apply Finset.sum_subtype
  intro m
  rw [GridRectangleBetween.mem_emptyRectangles]
  exact ⟨fun hm => ⟨hm, stabilizationMatchingEntry_advancing G s x a b hab e m he hm⟩,
    fun hm => hm.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- An entry, a transition and an exit count every three-rectangle matching path with the
product of its three weights. -/
theorem stabilizationWeightedExit_transition_entry_single_apply_eq_sum_paths
    (φ₁ φ₂ φ₃ : Finset (Fin (n + 1)) → LaurentPolynomial R) (x y : GridState n) :
    stabilizationWeightedExit G s φ₃
        (stabilizationWeightedTransition G s φ₂
          (stabilizationWeightedEntry G s φ₁ (single x 1))) y =
      ∑ p ∈ stabilizationMatchingThreePaths G s x y,
        φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns p.2.2.1.val.toGridRectangle) *
          φ₂ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.1.val.toGridRectangle) *
          φ₃ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.2.val.toGridRectangle) := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  let B (a : StabilizationMatchingNode G s) := { b : StabilizationMatchingNode G s // a ≠ b }
  let E (a : StabilizationMatchingNode G s) :=
    { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationMatchingTargetState G s a) // e.IsEmpty }
  let M (a b : StabilizationMatchingNode G s) :=
    { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
      m.IsEmpty ∧ m.top = (G.X s).castSucc }
  let F (b : StabilizationMatchingNode G s) :=
    { f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }
  let (a : StabilizationMatchingNode G s) :
      Fintype { b : StabilizationMatchingNode G s // a ≠ b } :=
    Fintype.ofFinite _
  let (a : StabilizationMatchingNode G s) : Fintype (E a) := Fintype.ofFinite _
  let (a b : StabilizationMatchingNode G s) : Fintype (M a b) := Fintype.ofFinite _
  let (b : StabilizationMatchingNode G s) : Fintype (F b) := Fintype.ofFinite _
  have huniv : stabilizationMatchingThreePaths G s x y =
      Finset.univ.sigma (fun a : StabilizationMatchingNode G s =>
        Finset.univ.sigma (fun b : B a =>
          (Finset.univ : Finset (E a)).product
            ((Finset.univ : Finset (M a b.val)).product (Finset.univ : Finset (F b.val))))) := by
    ext p
    constructor
    · intro _
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩⟩
    · intro _
      exact mem_stabilizationMatchingThreePaths G s p
  let C := fun (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) (a b : GridState (n + 1)) =>
    colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ a b
  let ce (a : StabilizationMatchingNode G s) :=
    C φ₁ (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s a)
  let cm (a b : StabilizationMatchingNode G s) :=
    C φ₂ a.val (stabilizationMatchingTargetState G s b)
  let cf (b : StabilizationMatchingNode G s) := C φ₃ b.val (y.insertPoint s.succ (G.X s).succ)
  have hdiag (a : StabilizationMatchingNode G s) :
      (∑ b : StabilizationMatchingNode G s, ce a * (if a = b then 0 else cm a b) * cf b) =
        ∑ b : B a, ce a * cm a b.val * cf b.val := by
    have hsub := Finset.sum_subtype (p := fun b => a ≠ b)
      (F := Fintype.ofFinite _) (Finset.univ.filter fun b => a ≠ b)
      (fun b => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun b => ce a * cm a b * cf b)
    rw [← hsub, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a = b <;> simp [h]
  rw [stabilizationWeightedExit_transition_entry_single_apply_eq_sum_nodes, huniv,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, ce a * (if a = b then 0 else cm a b) * cf b) = _
  rw [hdiag, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  have heq : ce a = ∑ e : E a,
      φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle) := by
    rw [show ce a = colRectCoeff _ φ₁ _ _ from rfl, colRectCoeff]
    exact Finset.sum_subtype _ (fun e => GridRectangleBetween.mem_emptyRectangles e) _
  rw [heq, Finset.sum_mul, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_product (Finset.univ : Finset (E a))
    ((Finset.univ : Finset (M a b.val)).product (Finset.univ : Finset (F b.val)))
    (fun p => φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.1.val.toGridRectangle) *
      φ₂ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns p.2.1.val.toGridRectangle) *
      φ₃ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.2.val.toGridRectangle))).symm
  apply Finset.sum_congr rfl
  intro e _
  have hmeq := colRectCoeff_eq_advancing_sum G s φ₂ a b.val b.property e.val e.property
  have hfeq : cf b.val = ∑ f : F b.val,
      φ₃ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle) := by
    rw [show cf b.val = colRectCoeff _ φ₃ _ _ from rfl, colRectCoeff]
    exact Finset.sum_subtype _ (fun f => GridRectangleBetween.mem_emptyRectangles f) _
  change _ * cm a b.val * cf b.val = _
  rw [show cm a b.val = colRectCoeff _ φ₂ _ _ from rfl, hmeq, hfeq]
  exact mul_sum_mul_sum'
    (φ₁ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle))
    (fun m : M a b.val =>
      φ₂ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns m.val.toGridRectangle))
    (fun f : F b.val =>
      φ₃ ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle))

end OnLeConjecture.KnotFloer.GridFull
