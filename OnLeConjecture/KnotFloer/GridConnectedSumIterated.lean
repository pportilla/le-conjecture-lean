/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnconditional
public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorReassociation
public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorReindex
public import OnLeConjecture.KnotFloer.GridFullCyclicRowsPower
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPreparation

/-!
# The iterated seam comparison into the finite tensor

Let `D₀, …, D_{N-1}` be prepared grid diagrams of sizes at least two: every size is a
successor, `D₀` has its `X` marking in the last column and the last row, and every other
factor has its `X` marking at the origin and the `O` marking of its last column in row
zero. The left-nested seam grid is defined by `T₀ = D₀` and
`T_{k+1} = connectedSumSeamGrid (rot T_k) D_{k+1}`, where `rot` relabels rows cyclically by
a chosen power that places the `X` marking of the last column in the last row. Its size
is `(∑ j, size D_j) - (N - 1)`.

Under the seam positive-path comparisons (M601), there is a chain map from the native
complex of the iterated seam grid to the finite tensor of the factor complexes over
`ZMod 2`, with shifts `(0,0)`, that carries the normalized class to the canonical finite
tensor class (M612). The inductive step composes the binary seam projection, the inverse
cyclic row relabeling (M615), and the insertion of the new factor into the finite tensor
(M609). The base case is the singleton tensor (M611). Since M601 is proved, the comparison
also holds without hypothesis.

Every grid of size at least two is related by grid moves to a prepared grid
(`exists_seamPrepared_movesTo`). This file does not identify the seam grid with a geometric
connected sum of knots (M613).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti TensorProduct CategoryTheory HomologicalComplex

section SeamMap

variable {n m : ℕ} {K : Type*} [Field K] [CharP K 2]
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
  (hpar : ∀ p q : SeamRetainedIndex n m,
    laurentEvalOne (seamRetainedDifferential G H hG hH K (Pi.single p 1) q) =
      (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : K) else 0) +
        if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : K) else 0)

/-- The Laurent-linear seam projection to the binary tensor: the corrected projection of
the seam contraction followed by the inverse tensor coordinates. -/
def seamTensorProjection :
    LaurentChain K (n + m + 1) →ₗ[LaurentPolynomial K]
      LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1) :=
  (seamTensorCoordinatesEquiv K).symm.toLinearMap ∘ₗ (seamFullContraction G H hG hH K).proj

include hO hpar in
/-- The seam projection preserves the Maslov degree. -/
theorem seamTensorProjection_mem_maslovPiece {r : ℤ} {c : LaurentChain K (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) K r) :
    seamTensorProjection G H hG hH c ∈ laurentTensorMaslovPiece (K := K) G H r := by
  have h := seamNativeTensorHomotopyEquiv_hom_apply G H hG hH hO hpar r
    ((laurentMaslovChainEquiv (connectedSumSeamGrid G H hG hH) K r).symm ⟨c, hc⟩)
  rw [LinearEquiv.apply_symm_apply] at h
  change (seamTensorCoordinatesEquiv K).symm ((seamFullContraction G H hG hH K).proj c) ∈ _
  rw [← h]
  exact (laurentTensorMaslovChainEquiv G H r _).property

include hO hpar in
/-- The seam projection intertwines the seam and binary tensor differentials. -/
theorem seamTensorProjection_differential (c : LaurentChain K (n + m + 1)) :
    seamTensorProjection G H hG hH (laurentDifferential (connectedSumSeamGrid G H hG hH) K c) =
      laurentTensorDifferential (K := K) G H (seamTensorProjection G H hG hH c) := by
  have hproj := LinearMap.congr_fun (seamFullContraction G H hG hH K).proj_comp_dM c
  have hcoord := LinearMap.congr_fun
    ((seamTensorCoordinates_intertwines_iff_evalOne G H hG hH hO).mpr hpar)
    ((seamTensorCoordinatesEquiv K).symm ((seamFullContraction G H hG hH K).proj c))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    at hproj hcoord
  change (seamTensorCoordinatesEquiv K).symm
      ((seamFullContraction G H hG hH K).proj (laurentDifferential _ K c)) =
    laurentTensorDifferential G H
      ((seamTensorCoordinatesEquiv K).symm ((seamFullContraction G H hG hH K).proj c))
  rw [hproj, hcoord, LinearEquiv.symm_apply_apply]

include hO in
/-- The seam projection preserves both filtration coordinates. -/
theorem seamTensorProjection_mem_bifiltrationLevel {a b : ℝ} {c : LaurentChain K (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) K a b) :
    seamTensorProjection G H hG hH c ∈ laurentTensorBifiltrationLevel (K := K) G H a b :=
  seamTensorCoordinatesEquiv_symm_mem_bifiltration G H hG hH hO
    (seamFullContraction_proj_mem_bifiltration_of_last_O G H hG hH hO K hc)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ι → ℕ} {D : ∀ i, GridDiagram (s i)}

/-- Precomposition of a Laurent tensor map with the seam projection. -/
def LaurentTensorFiniteMap.precompSeam (Ψ : LaurentTensorFiniteMap K G H D) :
    LaurentGridFiniteMap K (connectedSumSeamGrid G H hG hH) D where
  toLinearMap := Ψ.toLinearMap ∘ₗ seamTensorProjection G H hG hH
  mem_maslovPiece r c hc :=
    Ψ.mem_maslovPiece r _ (seamTensorProjection_mem_maslovPiece G H hG hH hO hpar hc)
  differential c := by
    simp only [LinearMap.comp_apply, seamTensorProjection_differential G H hG hH hO hpar,
      Ψ.differential]
  mem_bifiltrationLevel a b c hc :=
    Ψ.mem_bifiltrationLevel a b _ (seamTensorProjection_mem_bifiltrationLevel G H hG hH hO hc)

/-- The chain map of the precomposition is the seam projection followed by the tensor map. -/
theorem LaurentTensorFiniteMap.precompSeam_hom (Ψ : LaurentTensorFiniteMap K G H D) :
    (Ψ.precompSeam G H hG hH hO hpar).hom =
      (seamNativeTensorHomotopyEquiv G H hG hH hO hpar).hom ≫ Ψ.hom := by
  ext r : 1
  ext c
  apply (laurentFiniteMaslovChainEquiv D r).injective
  apply Subtype.ext
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply, LaurentGridFiniteMap.hom_apply,
    LaurentTensorFiniteMap.hom_apply, seamNativeTensorHomotopyEquiv_hom_apply]
  rfl

end SeamMap

section LeftRotation

variable {n : ℕ}

/-- Some power of the cyclic row translation places the `X` marking of the last column in
the last row. -/
theorem exists_seamLeftPower (G : GridDiagram (n + 1)) :
    ∃ k : ℕ, ((finRotate (n + 1)) ^ k) (G.X (Fin.last n)) = Fin.last n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Fin.ext ?_⟩
    have h := ((finRotate (0 + 1) ^ 0) (G.X (Fin.last 0))).isLt
    simp only [Fin.val_last]
    omega
  · exact exists_cyclicRows_send (by omega) _ _

/-- A chosen such power. -/
def seamLeftPower (G : GridDiagram (n + 1)) : ℕ := (exists_seamLeftPower G).choose

/-- The cyclic row relabeling that places the `X` marking of the last column in the last row. -/
abbrev seamLeftGrid (G : GridDiagram (n + 1)) : GridDiagram (n + 1) :=
  G.relabelRows ((finRotate (n + 1)) ^ seamLeftPower G)

theorem seamLeftGrid_X (G : GridDiagram (n + 1)) :
    (seamLeftGrid G).X (Fin.last n) = Fin.last n :=
  (exists_seamLeftPower G).choose_spec

/-- The left-normalized grid is obtained by grid moves. -/
theorem seamLeftGrid_movesTo (G : GridDiagram (n + 1)) : G.MovesTo (seamLeftGrid G) :=
  cyclicRows_pow_movesTo G _

end LeftRotation

section FinSnoc

/-- `Fin (M + 1)` is `Fin M` with the new last index. -/
abbrev finSnocInsertion (M : ℕ) : FactorInsertion (Fin M) (Fin (M + 1)) where
  embed := Fin.castSucc
  new := Fin.last M
  embed_injective := Fin.castSucc_injective M
  embed_ne_new := Fin.castSucc_ne_last
  cover k := by
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl rfl

/-- Assembly of a family over `Fin (M + 1)` by `Fin.snoc`. -/
def finSnocComb (M : ℕ) (β : Fin (M + 1) → Type*) : (finSnocInsertion M).Comb β where
  comb x e := Fin.snoc x e
  comb_embed x e i := Fin.snoc_castSucc e x i
  comb_new x e := Fin.snoc_last e x

end FinSnoc

section Chain

/-- The size, minus one, of the left-nested seam grid of a family of successor sizes. -/
def seamChainSize : (M : ℕ) → (Fin (M + 1) → ℕ) → ℕ
  | 0, p => p 0
  | M + 1, p => seamChainSize M (fun j => p j.castSucc) + p (Fin.last (M + 1))

/-- The left-nested seam grid of a family of grids whose factors after the first have
their `X` marking at the origin. -/
def seamChainGrid : (M : ℕ) → {p : Fin (M + 1) → ℕ} → (E : ∀ j, GridDiagram (p j + 1)) →
    (∀ j : Fin M, (E j.succ).X 0 = 0) → GridDiagram (seamChainSize M p + 1)
  | 0, _, E, _ => E 0
  | M + 1, _, E, hE =>
    connectedSumSeamGrid
      (seamLeftGrid (seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc)))
      (E (Fin.last (M + 1))) (seamLeftGrid_X _) (hE (Fin.last M))

theorem seamChainGrid_zero {p : Fin (0 + 1) → ℕ} (E : ∀ j, GridDiagram (p j + 1))
    (hE : ∀ j : Fin 0, (E j.succ).X 0 = 0) : seamChainGrid 0 E hE = E 0 := rfl

theorem seamChainGrid_succ (M : ℕ) {p : Fin (M + 1 + 1) → ℕ} (E : ∀ j, GridDiagram (p j + 1))
    (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0) :
    seamChainGrid (M + 1) E hE =
      connectedSumSeamGrid
        (seamLeftGrid (seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc)))
        (E (Fin.last (M + 1))) (seamLeftGrid_X _) (hE (Fin.last M)) := rfl

theorem seamChainSize_eq_sum : (M : ℕ) → (p : Fin (M + 1) → ℕ) →
    seamChainSize M p = ∑ j, p j
  | 0, p => by simp [seamChainSize]
  | M + 1, p => by
    rw [seamChainSize, seamChainSize_eq_sum M]
    conv_rhs => rw [Fin.sum_univ_castSucc]

theorem one_le_seamChainSize (M : ℕ) {p : Fin (M + 1) → ℕ} (hp : ∀ j, 1 ≤ p j) :
    1 ≤ seamChainSize M p := by
  rw [seamChainSize_eq_sum]
  exact (hp 0).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (Finset.mem_univ 0))

theorem two_le_seamChainSize (M : ℕ) {p : Fin (M + 1) → ℕ} (hp : ∀ j, 1 ≤ p j) :
    2 ≤ seamChainSize M p + 1 := by
  have := one_le_seamChainSize M hp
  omega

/-- Homology of a composite, evaluated on a class. -/
theorem homologyMap_comp_apply {K : Type*} [Field K] {C D E : ChainComplex (ModuleCat K) ℤ}
    (φ : C ⟶ D) (ψ : D ⟶ E) (x : C.homology 0) :
    homologyMap (φ ≫ ψ) 0 x = homologyMap ψ 0 (homologyMap φ 0 x) := by
  rw [homologyMap_comp, ModuleCat.comp_apply]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The comparison for the left-nested seam grid of a prepared family with successor sizes,
under the seam positive-path comparisons. -/
theorem exists_seamChain_finiteTensor_map
    (hpar : ∀ n m : ℕ, SeamPositivePathComparisons n m) :
    (M : ℕ) → {p : Fin (M + 1) → ℕ} → (E : ∀ j, GridDiagram (p j + 1)) →
      (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) →
      (∀ j : Fin M, (E j.succ).O (Fin.last (p j.succ)) = 0) → (hp : ∀ j, 1 ≤ p j) →
      ∃ F : LaurentGridFiniteMap (ZMod 2) (seamChainGrid M E hE) E,
        homologyMap F.hom 0
            (gridCanonicalClass (seamChainGrid M E hE) (two_le_seamChainSize M hp)) =
          gridCanonicalFiniteTensorClass E (fun j => by have := hp j; omega)
  | 0, p, E, hE, _, hp => by
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    refine ⟨laurentFiniteSubsingletonMap 0 E, ?_⟩
    have h1 := laurentFiniteSubsingletonMap_hom (K := ZMod 2) (0 : Fin (0 + 1)) E
    have h2 := laurentFiniteMaslovSubsingletonIso_hom_canonicalClass (0 : Fin (0 + 1)) E
      (fun j => by have := hp j; omega)
    rw [← h1] at h2
    exact h2
  | M + 1, p, E, hE, hEO, hp => by
    obtain ⟨F', hF'⟩ := exists_seamChain_finiteTensor_map hpar M (fun j => E j.castSucc)
      (fun j => hE j.castSucc) (fun j => hEO j.castSucc) (fun j => hp j.castSucc)
    have hD : ∀ j, 2 ≤ p j + 1 := fun j => by have := hp j; omega
    have hT' : 2 ≤ seamChainSize M (fun j => p j.castSucc) + 1 :=
      two_le_seamChainSize M (fun j => hp j.castSucc)
    rw [seamChainGrid_succ]
    generalize seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc) = T' at F' hF' ⊢
    obtain ⟨F'', hF''hom⟩ : ∃ F'' : LaurentGridFiniteMap (ZMod 2) (seamLeftGrid T')
        (fun j : Fin (M + 1) => E j.castSucc),
        F''.hom = (laurentMaslovCyclicRowsPowIso T' (seamLeftPower T')).inv ≫ F'.hom :=
      ⟨F'.precomp ((laurentCyclicRowsPowEquiv (ZMod 2) (seamLeftPower T')).symm.toLinearMap)
        (fun r c hc => laurentCyclicRowsPowEquiv_symm_mem_maslovPiece T' (ZMod 2) _ hc)
        (fun c => laurentCyclicRowsPowEquiv_symm_differential T' (ZMod 2) _ c)
        (fun a b c hc => laurentCyclicRowsPowEquiv_symm_mem_bifiltrationLevel T' (ZMod 2) _ hc),
        LaurentGridFiniteMap.precomp_hom F' _ _ _ _ _
          (fun r c => laurentMaslovCyclicRowsPowIso_inv_apply T' _ r c)⟩
    have hF'' : homologyMap F''.hom 0 (gridCanonicalClass (seamLeftGrid T') hT') =
        gridCanonicalFiniteTensorClass (fun j : Fin (M + 1) => E j.castSucc)
          (fun j => hD j.castSucc) := by
      rw [hF''hom, homologyMap_comp_apply, gridCanonicalClass_cyclicRowsPow_inv T' hT']
      exact hF'
    have hΨ := F''.insertTensor_canonicalClass (finSnocInsertion (M + 1)) E
      (finSnocComb (M + 1) (fun j => LaurentChain (ZMod 2) (p j + 1))) hD hT' hF''
    have hpar₂ := seamParity_of_positivePaths (hpar _ _) (seamLeftGrid T') (E (Fin.last (M + 1)))
      (seamLeftGrid_X T') (hE (Fin.last M)) (hEO (Fin.last M))
    obtain ⟨θ, hθ⟩ : ∃ θ : LaurentGridFiniteMap (ZMod 2)
        (connectedSumSeamGrid (seamLeftGrid T') (E (Fin.last (M + 1))) (seamLeftGrid_X T')
          (hE (Fin.last M))) E,
        θ.hom = (seamNativeTensorHomotopyEquiv (seamLeftGrid T') (E (Fin.last (M + 1)))
          (seamLeftGrid_X T') (hE (Fin.last M)) (hEO (Fin.last M)) hpar₂).hom ≫
            (F''.insertTensor (finSnocInsertion (M + 1)) E
              (finSnocComb (M + 1) (fun j => LaurentChain (ZMod 2) (p j + 1)))).hom :=
      ⟨LaurentTensorFiniteMap.precompSeam (seamLeftGrid T') (E (Fin.last (M + 1)))
        (seamLeftGrid_X T') (hE (Fin.last M)) (hEO (Fin.last M)) hpar₂
        (F''.insertTensor (finSnocInsertion (M + 1)) E
          (finSnocComb (M + 1) (fun j => LaurentChain (ZMod 2) (p j + 1)))),
        LaurentTensorFiniteMap.precompSeam_hom _ _ _ _ _ _ _⟩
    have hs := seamNativeTensor_hom_canonicalClass (seamLeftGrid T') (E (Fin.last (M + 1)))
      (seamLeftGrid_X T') (hE (Fin.last M)) (hEO (Fin.last M)) hpar₂ hT' (hD _)
    have key : homologyMap θ.hom 0 (gridCanonicalClass (connectedSumSeamGrid (seamLeftGrid T')
        (E (Fin.last (M + 1))) (seamLeftGrid_X T') (hE (Fin.last M))) (by omega)) =
        gridCanonicalFiniteTensorClass E hD := by
      rw [hθ]
      refine (homologyMap_comp_apply _ _ _).trans ?_
      exact (congrArg (fun x => homologyMap (F''.insertTensor (finSnocInsertion (M + 1)) E
        (finSnocComb (M + 1) (fun j => LaurentChain (ZMod 2) (p j + 1)))).hom 0 x) hs).trans hΨ
    exact ⟨θ, key⟩

end Chain

section Iterated

/-- Transport of a grid diagram along an equality of sizes. -/
def gridCast {n n' : ℕ} (h : n = n') (G : GridDiagram n) : GridDiagram n' := h ▸ G

theorem gridCast_sigma {n n' : ℕ} (h : n = n') (G : GridDiagram n) :
    (⟨n', gridCast h G⟩ : Σ k, GridDiagram k) = ⟨n, G⟩ := by
  subst h
  rfl

theorem movesTo_gridCast {n n' : ℕ} (h : n = n') (G : GridDiagram n) :
    G.MovesTo (gridCast h G) := by
  subst h
  exact GridDiagram.MovesTo.refl G

theorem gridCast_X_zero_iff {n m : ℕ} (h : n = m + 1) (G : GridDiagram n) :
    (gridCast h G).X 0 = 0 ↔ G.X ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  subst h
  rfl

theorem gridCast_O_last_iff {n m : ℕ} (h : n = m + 1) (G : GridDiagram n) :
    (gridCast h G).O (Fin.last m) = 0 ↔ G.O ⟨m, by omega⟩ = ⟨0, by omega⟩ := by
  subst h
  rfl

/-- The native complexes of a grid and of its size transport are isomorphic. -/
def laurentMaslovGridCastIso {K : Type*} [Field K] [CharP K 2] {n n' : ℕ} (h : n = n')
    (G : GridDiagram n) : laurentMaslovComplex G K ≅ laurentMaslovComplex (gridCast h G) K := by
  subst h
  exact Iso.refl _

theorem laurentMaslovGridCastIso_inv_shifts {K : Type*} [Field K] [CharP K 2] {n n' : ℕ}
    (h : n = n') (G : GridDiagram n) :
    (laurentMaslovBifiltration (gridCast h G) K).Shifts (laurentMaslovBifiltration G K)
      (laurentMaslovGridCastIso h G).inv 0 0 := by
  subst h
  intro a b r x hx
  rw [add_zero, add_zero]
  exact hx

theorem gridCanonicalClass_gridCastIso_inv {n n' : ℕ} (h : n = n') (G : GridDiagram n)
    (hn : 2 ≤ n) (hn' : 2 ≤ n') :
    homologyMap (laurentMaslovGridCastIso (K := ZMod 2) h G).inv 0
        (gridCanonicalClass (gridCast h G) hn') =
      gridCanonicalClass G hn :=
  gridCanonicalClass_homotopyEquiv _ G hn' hn
    (HomotopyEquiv.ofIso (laurentMaslovGridCastIso h G).symm) 0
    (laurentMaslovGridCastIso_inv_shifts h G)

/-- Prepared factors for the iterated seam: every size is a successor, the first factor has
its `X` marking in the last column and the last row, and every other factor has its `X`
marking at the origin and the `O` marking of its last column in row zero. -/
structure SeamPrepared {N : ℕ} {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j)) : Prop where
  pos : ∀ j, 0 < sizes j
  first : ∀ h : 0 < N, (D ⟨0, h⟩).X ⟨sizes ⟨0, h⟩ - 1, Nat.sub_lt (pos _) Nat.one_pos⟩ =
    ⟨sizes ⟨0, h⟩ - 1, Nat.sub_lt (pos _) Nat.one_pos⟩
  rest : ∀ j : Fin N, j.val ≠ 0 → (D j).X ⟨0, pos j⟩ = ⟨0, pos j⟩ ∧
    (D j).O ⟨sizes j - 1, Nat.sub_lt (pos j) Nat.one_pos⟩ = ⟨0, pos j⟩

/-- The size of the iterated seam grid: one row and one column are shared at each seam. -/
def iteratedSeamSize {N : ℕ} (sizes : Fin N → ℕ) : ℕ := (∑ j, sizes j) - (N - 1)

/-- The unique grid diagram of size zero. -/
def gridZero : GridDiagram 0 where
  O := ⟨1⟩
  X := ⟨1⟩
  disjoint c := c.elim0

theorem iteratedSeamSize_zero (sizes : Fin 0 → ℕ) : iteratedSeamSize sizes = 0 := by
  simp [iteratedSeamSize]

/-- The prepared factors, with their successor sizes made explicit. -/
def preparedCast {N : ℕ} {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) (j : Fin N) : GridDiagram (sizes j - 1 + 1) :=
  gridCast (by have := hprep.pos j; omega) (D j)

theorem preparedCast_X {M : ℕ} {sizes : Fin (M + 1) → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) (j : Fin M) : (preparedCast D hprep j.succ).X 0 = 0 :=
  (gridCast_X_zero_iff _ (D j.succ)).mpr (hprep.rest j.succ (Nat.succ_ne_zero _)).1

theorem preparedCast_O {M : ℕ} {sizes : Fin (M + 1) → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) (j : Fin M) :
    (preparedCast D hprep j.succ).O (Fin.last (sizes j.succ - 1)) = 0 :=
  (gridCast_O_last_iff _ (D j.succ)).mpr (hprep.rest j.succ (Nat.succ_ne_zero _)).2

theorem preparedCast_sigma {N : ℕ} {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) :
    (fun j => (⟨sizes j - 1 + 1, preparedCast D hprep j⟩ : Σ k, GridDiagram k)) =
      fun j => ⟨sizes j, D j⟩ :=
  funext fun j => gridCast_sigma _ (D j)

theorem iteratedSeamSize_succ {M : ℕ} {sizes : Fin (M + 1) → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) :
    seamChainSize M (fun j => sizes j - 1) + 1 = iteratedSeamSize sizes := by
  rw [seamChainSize_eq_sum, iteratedSeamSize]
  have h : ∑ j, sizes j = ∑ j, (sizes j - 1) + (M + 1) := by
    calc ∑ j, sizes j = ∑ j, ((sizes j - 1) + 1) :=
          Finset.sum_congr rfl fun j _ => by have := hprep.pos j; omega
      _ = ∑ j, (sizes j - 1) + ∑ _j : Fin (M + 1), 1 := Finset.sum_add_distrib
      _ = ∑ j, (sizes j - 1) + (M + 1) := by simp
  omega

/-- The left-nested iterated seam grid of a prepared family. -/
def iteratedSeamGrid : {N : ℕ} → {sizes : Fin N → ℕ} → (D : ∀ j, GridDiagram (sizes j)) →
    SeamPrepared D → GridDiagram (iteratedSeamSize sizes)
  | 0, sizes, _, _ => gridCast (iteratedSeamSize_zero sizes).symm gridZero
  | M + 1, _, D, hprep =>
    gridCast (iteratedSeamSize_succ D hprep)
      (seamChainGrid M (preparedCast D hprep) (preparedCast_X D hprep))

theorem iteratedSeamGrid_succ {M : ℕ} {sizes : Fin (M + 1) → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hprep : SeamPrepared D) :
    iteratedSeamGrid D hprep = gridCast (iteratedSeamSize_succ D hprep)
      (seamChainGrid M (preparedCast D hprep) (preparedCast_X D hprep)) := rfl

/-- The iterated seam grid of a nonempty family of grids of sizes at least two has size at
least two. -/
theorem two_le_iteratedSeamSize {N : ℕ} (hN : 0 < N) {sizes : Fin N → ℕ}
    (hD : ∀ j, 2 ≤ sizes j) : 2 ≤ iteratedSeamSize sizes := by
  have h : Finset.univ.card • 2 ≤ ∑ j, sizes j :=
    Finset.card_nsmul_le_sum Finset.univ sizes 2 fun j _ => hD j
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [iteratedSeamSize]
  omega

private theorem exists_prepared_factor {N : ℕ} (j : Fin N) {s : ℕ} (G : GridDiagram s)
    (hs : 2 ≤ s) :
    ∃ (s' : ℕ) (G' : GridDiagram s') (hpos : 0 < s'),
      (j.val = 0 → G'.X ⟨s' - 1, Nat.sub_lt hpos Nat.one_pos⟩ =
        ⟨s' - 1, Nat.sub_lt hpos Nat.one_pos⟩) ∧
      (j.val ≠ 0 → G'.X ⟨0, hpos⟩ = ⟨0, hpos⟩ ∧
        G'.O ⟨s' - 1, Nat.sub_lt hpos Nat.one_pos⟩ = ⟨0, hpos⟩) ∧
      2 ≤ s' ∧ G.MovesTo G' := by
  by_cases hj : j.val = 0
  · obtain ⟨k, hk⟩ := exists_cyclicRows_send hs (G.X ⟨s - 1, by omega⟩) ⟨s - 1, by omega⟩
    exact ⟨s, G.relabelRows ((finRotate s) ^ k), by omega, fun _ => hk,
      fun h => absurd hj h, hs, cyclicRows_pow_movesTo G k⟩
  · have hs' : s = s - 1 + 1 := by omega
    obtain ⟨H, hm, hX, hO, _⟩ := exists_seamPreparedGrid (gridCast hs' G)
    refine ⟨s - 1 + 2, H, by omega, fun h => absurd h hj, fun _ => ⟨hX, ?_⟩, by omega,
      (movesTo_gridCast hs' G).trans hm⟩
    have he : (⟨s - 1 + 2 - 1, Nat.sub_lt (by omega) Nat.one_pos⟩ : Fin (s - 1 + 2)) =
        Fin.last (s - 1 + 1) := Fin.ext (by simp)
    rw [he, hO]
    rfl

/-- Every family of grids of sizes at least two is related factorwise by grid moves to a
prepared family of grids of sizes at least two. -/
theorem exists_seamPrepared_movesTo {N : ℕ} {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j))
    (hD : ∀ j, 2 ≤ sizes j) :
    ∃ (sizes' : Fin N → ℕ) (D' : ∀ j, GridDiagram (sizes' j)),
      SeamPrepared D' ∧ (∀ j, 2 ≤ sizes' j) ∧ ∀ j, (D j).MovesTo (D' j) := by
  choose sizes' D' hpos hfirst hrest h2 hm using fun j => exists_prepared_factor j (D j) (hD j)
  exact ⟨sizes', D', ⟨hpos, fun h => hfirst ⟨0, h⟩ rfl, fun j hj => hrest j hj⟩, h2, hm⟩

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The iterated seam comparison (M612), conditional on the seam positive-path comparisons:
a chain map from the native complex of the iterated seam grid to the finite tensor of the
factor complexes, with shifts `(0,0)`, that carries the normalized class to the canonical
finite tensor class. -/
theorem exists_iteratedSeam_finiteTensor_map_of_parity
    (hpar : ∀ n m : ℕ, SeamPositivePathComparisons n m) {N : ℕ} (hN : 0 < N)
    {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j)) (hD : ∀ j, 2 ≤ sizes j)
    (hprep : SeamPrepared D) :
    ∃ θ : laurentMaslovComplex (iteratedSeamGrid D hprep) (ZMod 2) ⟶
        laurentFiniteMaslovComplex (K := ZMod 2) D,
      (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)).Shifts
          (laurentFiniteMaslovBifiltration D) θ 0 0 ∧
        homologyMap θ 0
            (gridCanonicalClass (iteratedSeamGrid D hprep) (two_le_iteratedSeamSize hN hD)) =
          gridCanonicalFiniteTensorClass D hD := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hp : ∀ j, 1 ≤ sizes j - 1 := fun j => by have := hD j; omega
  obtain ⟨F, hF⟩ := exists_seamChain_finiteTensor_map hpar M (preparedCast D hprep)
    (preparedCast_X D hprep) (preparedCast_O D hprep) hp
  have hsz := iteratedSeamSize_succ D hprep
  rw [iteratedSeamGrid_succ]
  generalize seamChainGrid M (preparedCast D hprep) (preparedCast_X D hprep) = T at F hF ⊢
  refine ⟨(laurentMaslovGridCastIso hsz T).inv ≫ F.hom ≫
    (laurentFiniteMaslovFamilyIso (preparedCast_sigma D hprep)).hom, ?_, ?_⟩
  · have h := (laurentMaslovGridCastIso_inv_shifts (K := ZMod 2) hsz T).comp
      (F.hom_shifts.comp (laurentFiniteMaslovFamilyIso_hom_shifts (preparedCast_sigma D hprep)))
    simp only [add_zero] at h
    exact h
  · rw [homologyMap_comp_apply, homologyMap_comp_apply,
      gridCanonicalClass_gridCastIso_inv hsz T (two_le_seamChainSize M hp), hF]
    exact laurentFiniteMaslovFamilyIso_hom_canonicalClass (preparedCast_sigma D hprep) _ hD

/-- The iterated seam comparison (M612), without hypothesis. -/
theorem exists_iteratedSeam_finiteTensor_map {N : ℕ} (hN : 0 < N)
    {sizes : Fin N → ℕ} (D : ∀ j, GridDiagram (sizes j)) (hD : ∀ j, 2 ≤ sizes j)
    (hprep : SeamPrepared D) :
    ∃ θ : laurentMaslovComplex (iteratedSeamGrid D hprep) (ZMod 2) ⟶
        laurentFiniteMaslovComplex (K := ZMod 2) D,
      (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)).Shifts
          (laurentFiniteMaslovBifiltration D) θ 0 0 ∧
        homologyMap θ 0
            (gridCanonicalClass (iteratedSeamGrid D hprep) (two_le_iteratedSeamSize hN hD)) =
          gridCanonicalFiniteTensorClass D hD :=
  exists_iteratedSeam_finiteTensor_map_of_parity seamPositivePathComparisons hN D hD hprep

end Iterated

end OnLeConjecture.KnotFloer.GridFull
