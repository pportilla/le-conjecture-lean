/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The determinant pairing of colour derivatives and O switches

This module formalizes the linear algebra of equation `determinant-pairing` of Section 4 of the
written proof of Statement E (`statement_E_complete_proof.tex`) and the incidence determinant of
Lemma `scissorIncidenceForest` of Section 9.

* `derivativeProduct_comp_switch`: if every operator `Ψ c` satisfies
  `Ψ c ∘ F e = F e ∘ Ψ c + b c e • K e` and commutes with every `K e`, then a product of
  `m + 1` operators `Ψ` passes a map `F e` with one correction term for each factor `Ψ`. This is
  the commutator identity `colour-switch-commutator` of the written proof, iterated.
* `derivativeProduct_switchProduct_of_lt`: if every `Ψ c` annihilates `x₀`, then a product of
  `m` operators `Ψ` annihilates `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` whenever `d < m`.
* `derivativeProduct_switchProduct_eq_det`: in characteristic two, a product of `d` operators
  `Ψ` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `det B` times `K (d - 1) ∘ ⋯ ∘ K 0`
  applied to `x₀`, where `B r e = b (c r) e`. This is equation `determinant-pairing`. The proof
  is a Laplace expansion along the last column, in which every sign equals one.
* `det_forestIncidence`: the incidence matrix of a rooted forest with the root rows removed has
  determinant one over every commutative ring. Its columns are indexed by the non-root vertices,
  each of which names the edge to its parent.
* `det_starIncidence`: the edges selected by the star rule at one rank (Lemma
  `scissorIncidenceForest`) have an incidence matrix of determinant one, because the selection
  forms a rooted forest.
* `derivativeProduct_switchProduct_eq_of_forest`: in characteristic two, if the matrix `B` is a
  forest incidence matrix after renaming its rows and columns, then the product of the operators
  `Ψ` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `K (d - 1) ∘ ⋯ ∘ K 0` applied to `x₀`.
  `derivativeProduct_switchProduct_eq_of_star` is the same statement for the star selection.

In the written proof the module `M` is the direct sum of the homology groups of the grids along
the sequence of moves, and the operators are the maps induced on homology.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open Finset Matrix

/-! ### Products of colour derivatives and of switches -/

section Products

variable {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The product `Ψ (c 0) ∘ Ψ (c 1) ∘ ⋯ ∘ Ψ (c (m - 1))` of the operators `Ψ` indexed by a
sequence `c` of `m` colours. The empty product is the identity map. -/
def derivativeProduct (Ψ : C → M →ₗ[R] M) : {m : ℕ} → (Fin m → C) → M →ₗ[R] M
  | 0, _ => LinearMap.id
  | _ + 1, c => Ψ (c 0) ∘ₗ derivativeProduct Ψ (Fin.tail c)

/-- The product `F (d - 1) ∘ ⋯ ∘ F 1 ∘ F 0` of the first `d` maps of a sequence `F`. The empty
product is the identity map. -/
def switchProduct (F : ℕ → M →ₗ[R] M) : ℕ → M →ₗ[R] M
  | 0 => LinearMap.id
  | d + 1 => F d ∘ₗ switchProduct F d

/-- The product of the operators indexed by the empty sequence of colours is the identity. -/
@[simp]
theorem derivativeProduct_zero (Ψ : C → M →ₗ[R] M) (c : Fin 0 → C) :
    derivativeProduct Ψ c = LinearMap.id :=
  rfl

/-- A product of `m + 1` operators is its first factor followed by the product of the others. -/
theorem derivativeProduct_succ (Ψ : C → M →ₗ[R] M) {m : ℕ} (c : Fin (m + 1) → C) :
    derivativeProduct Ψ c = Ψ (c 0) ∘ₗ derivativeProduct Ψ (Fin.tail c) :=
  rfl

/-- The empty product of maps is the identity. -/
@[simp]
theorem switchProduct_zero (F : ℕ → M →ₗ[R] M) : switchProduct F 0 = LinearMap.id :=
  rfl

/-- The product of the first `d + 1` maps is `F d` composed with the product of the first `d`. -/
theorem switchProduct_succ (F : ℕ → M →ₗ[R] M) (d : ℕ) :
    switchProduct F (d + 1) = F d ∘ₗ switchProduct F d :=
  rfl

/-- Omitting the factor at position `r + 1` from a product of `m + 2` operators leaves the first
factor followed by the product of the remaining factors with position `r` of the tail omitted. -/
theorem derivativeProduct_comp_succ_succAbove (Ψ : C → M →ₗ[R] M) {m : ℕ}
    (c : Fin (m + 2) → C) (r : Fin (m + 1)) :
    derivativeProduct Ψ (c ∘ r.succ.succAbove) =
      Ψ (c 0) ∘ₗ derivativeProduct Ψ (Fin.tail c ∘ r.succAbove) := by
  have h0 : (c ∘ r.succ.succAbove) 0 = c 0 := by simp
  have ht : Fin.tail (c ∘ r.succ.succAbove) = Fin.tail c ∘ r.succAbove := by
    funext i
    simp [Fin.tail]
  rw [derivativeProduct_succ, h0, ht]

end Products

/-! ### The commutation formula and the determinant pairing -/

section Pairing

variable {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Ψ : C → M →ₗ[R] M} {F K : ℕ → M →ₗ[R] M} {b : C → ℕ → R} {x₀ : M}

/-- If every operator `Ψ c` satisfies `Ψ c ∘ F e = F e ∘ Ψ c + b c e • K e` and commutes with
every `K e`, then a product of `m + 1` operators `Ψ` passes `F e` with one correction term for
each factor. The correction term of the factor at position `r` is `b (c r) e • K e` followed by
the product of the other factors. -/
theorem derivativeProduct_comp_switch (hF : ∀ c e, Ψ c ∘ₗ F e = F e ∘ₗ Ψ c + b c e • K e)
    (hK : ∀ c e, Ψ c ∘ₗ K e = K e ∘ₗ Ψ c) {m : ℕ} (c : Fin (m + 1) → C) (e : ℕ) :
    derivativeProduct Ψ c ∘ₗ F e = F e ∘ₗ derivativeProduct Ψ c +
      ∑ r : Fin (m + 1), b (c r) e • (K e ∘ₗ derivativeProduct Ψ (c ∘ r.succAbove)) := by
  have hF' : ∀ c e x, Ψ c (F e x) = F e (Ψ c x) + b c e • K e x := fun c e x => by
    simpa using LinearMap.congr_fun (hF c e) x
  have hK' : ∀ c e x, Ψ c (K e x) = K e (Ψ c x) := fun c e x => by
    simpa using LinearMap.congr_fun (hK c e) x
  induction m with
  | zero =>
    ext x
    simp [derivativeProduct_succ, hF']
  | succ m ih =>
    ext x
    have h := LinearMap.congr_fun (ih (Fin.tail c)) x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] at h
    rw [Fin.sum_univ_succ, Fin.succAbove_zero]
    simp only [derivativeProduct_comp_succ_succAbove, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rw [derivativeProduct_succ, LinearMap.comp_apply, h, map_add, hF', map_sum]
    simp only [map_smul, hK']
    rw [add_assoc]
    rfl

/-- If every operator `Ψ c` annihilates `x₀`, then every nonempty product of operators `Ψ`
annihilates `x₀`. -/
theorem derivativeProduct_apply_eq_zero (hx : ∀ c, Ψ c x₀ = 0) {m : ℕ} (c : Fin (m + 1) → C) :
    derivativeProduct Ψ c x₀ = 0 := by
  induction m with
  | zero => simp [derivativeProduct_succ, hx]
  | succ m ih => rw [derivativeProduct_succ, LinearMap.comp_apply, ih, map_zero]

variable (hF : ∀ c e, Ψ c ∘ₗ F e = F e ∘ₗ Ψ c + b c e • K e)
  (hK : ∀ c e, Ψ c ∘ₗ K e = K e ∘ₗ Ψ c) (hx : ∀ c, Ψ c x₀ = 0)
include hF hK hx

/-- A product of `m` operators `Ψ` annihilates `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` when
`d < m`, that is, when there are more operators `Ψ` than maps `F`. -/
theorem derivativeProduct_switchProduct_of_lt {m d : ℕ} (c : Fin m → C) (h : d < m) :
    derivativeProduct Ψ c (switchProduct F d x₀) = 0 := by
  induction d generalizing m with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact derivativeProduct_apply_eq_zero hx c
  | succ d ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [switchProduct_succ, LinearMap.comp_apply, ← LinearMap.comp_apply (derivativeProduct Ψ c),
      derivativeProduct_comp_switch hF hK]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply]
    rw [ih c (by omega), map_zero, zero_add]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [ih (c ∘ r.succAbove) (by omega), map_zero, smul_zero]

/-- **The determinant pairing.** In characteristic two, a product of `d` operators `Ψ` indexed
by the colours `c` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `det B` times
`K (d - 1) ∘ ⋯ ∘ K 0` applied to `x₀`, where `B r e = b (c r) e`. -/
theorem derivativeProduct_switchProduct_eq_det [CharP R 2] {d : ℕ} (c : Fin d → C) :
    derivativeProduct Ψ c (switchProduct F d x₀) =
      (Matrix.of fun r e : Fin d => b (c r) e).det • switchProduct K d x₀ := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [switchProduct_succ, LinearMap.comp_apply, ← LinearMap.comp_apply (derivativeProduct Ψ c),
      derivativeProduct_comp_switch hF hK]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply]
    rw [derivativeProduct_switchProduct_of_lt hF hK hx c (Nat.lt_succ_self d), map_zero,
      zero_add]
    simp only [ih, map_smul, smul_smul, ← Finset.sum_smul, switchProduct_succ,
      LinearMap.comp_apply]
    congr 1
    rw [Matrix.det_succ_column _ (Fin.last d)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CharTwo.neg_eq, one_pow, one_mul, Matrix.of_apply, Fin.val_last]
    congr 2
    ext r e
    simp [Fin.succAbove_last]

/-- In characteristic two, if `K (d - 1) ∘ ⋯ ∘ K 0` sends `x₀` to a prescribed element `y`, then
the product of `d` operators `Ψ` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `det B • y`. -/
theorem derivativeProduct_switchProduct_eq_det_smul [CharP R 2] {d : ℕ} (c : Fin d → C) {y : M}
    (hy : switchProduct K d x₀ = y) :
    derivativeProduct Ψ c (switchProduct F d x₀) =
      (Matrix.of fun r e : Fin d => b (c r) e).det • y := by
  rw [derivativeProduct_switchProduct_eq_det hF hK hx c, hy]

/-- In characteristic two, if `det B = 1` and `K (d - 1) ∘ ⋯ ∘ K 0` sends `x₀` to `y`, then the
product of `d` operators `Ψ` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `y`. -/
theorem derivativeProduct_switchProduct_eq_of_det_eq_one [CharP R 2] {d : ℕ} (c : Fin d → C)
    {y : M} (hdet : (Matrix.of fun r e : Fin d => b (c r) e).det = 1)
    (hy : switchProduct K d x₀ = y) :
    derivativeProduct Ψ c (switchProduct F d x₀) = y := by
  rw [derivativeProduct_switchProduct_eq_det_smul hF hK hx c hy, hdet, one_smul]

end Pairing

/-! ### Rooted forests -/

section Forest

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

/-- The reduced incidence matrix of a rooted forest. The non-root vertices index both the rows
and the columns. The column of a vertex `e` is the edge from `e` to its parent, and
`parent e = none` means that this parent is the root. The entry in row `c` and column `e` is the
indicator of `c = e` plus the indicator of `parent e = some c`. -/
def forestIncidence (parent : V → Option V) : Matrix V V R :=
  Matrix.of fun c e => (if c = e then 1 else 0) + if parent e = some c then 1 else 0

/-- **The reduced incidence matrix of a rooted forest has determinant one.** Here `parent`
describes a rooted forest whose non-root vertices form `V`, and `depth` strictly increases from
a parent to its child. -/
theorem det_forestIncidence (parent : V → Option V) (depth : V → ℕ)
    (hdepth : ∀ v w, parent v = some w → depth w < depth v) :
    (Matrix.of fun c e : V =>
      (if c = e then (1 : R) else 0) + if parent e = some c then 1 else 0).det = 1 := by
  -- The matrix is block triangular with respect to `depth`, and every diagonal block is an
  -- identity matrix.
  set B : Matrix V V R :=
    Matrix.of fun c e : V => (if c = e then (1 : R) else 0) + if parent e = some c then 1 else 0
  have htri : B.BlockTriangular depth := by
    intro c e hce
    have hne : c ≠ e := by
      rintro rfl
      exact lt_irrefl _ hce
    have hp : parent e ≠ some c := fun h => lt_asymm hce (hdepth e c h)
    simp [B, hne, hp]
  rw [htri.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have hblock : B.toSquareBlock depth k = 1 := by
    ext ⟨c, hc⟩ ⟨e, he⟩
    by_cases hce : c = e
    · subst hce
      have hp : parent c ≠ some c := fun h => lt_irrefl _ (hdepth c c h)
      simp [B, Matrix.toSquareBlock_def, hp]
    · have hp : parent e ≠ some c := fun h => by
        have := hdepth e c h
        omega
      have hne : (⟨c, hc⟩ : {a // depth a = k}) ≠ ⟨e, he⟩ := fun h => hce (congrArg Subtype.val h)
      simp [B, Matrix.toSquareBlock_def, hce, hp, Matrix.one_apply_ne hne]
  rw [hblock, Matrix.det_one]

/-- The matrix `forestIncidence parent` has determinant one when `parent` admits a depth
function. -/
theorem forestIncidence_det (parent : V → Option V) (depth : V → ℕ)
    (hdepth : ∀ v w, parent v = some w → depth w < depth v) :
    (forestIncidence parent : Matrix V V R).det = 1 :=
  det_forestIncidence parent depth hdepth

/-- In characteristic two, renaming the rows and the columns of a square matrix by two
bijections does not change its determinant. -/
theorem det_submatrix_equiv_charTwo [CharP R 2] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix V V R) (σ τ : n ≃ V) : (A.submatrix σ τ).det = A.det := by
  have hsub : A.submatrix σ τ = (A.submatrix σ σ).submatrix id (τ.trans σ.symm) := by
    ext i j
    simp
  rw [hsub, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (τ.trans σ.symm)) with h | h
  · rw [h]
    simp
  · rw [h]
    simp [CharTwo.neg_eq]

end Forest

/-! ### The determinant pairing for a forest of O switches -/

section ForestPairing

variable {R M C V : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]
  [DecidableEq V]
variable {Ψ : C → M →ₗ[R] M} {F K : ℕ → M →ₗ[R] M} {b : C → ℕ → R} {x₀ : M}

/-- **The determinant pairing for a forest.** In characteristic two, suppose that the colours
`c r` and the maps `F e` are renamed by bijections `σ` and `τ` onto the non-root vertices of a
rooted forest, so that `b (c r) e` is the entry of the reduced forest incidence matrix in row
`σ r` and column `τ e`. If `K (d - 1) ∘ ⋯ ∘ K 0` sends `x₀` to `y`, then the product of the
operators `Ψ (c r)` sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `y`. -/
theorem derivativeProduct_switchProduct_eq_of_forest
    (hF : ∀ c e, Ψ c ∘ₗ F e = F e ∘ₗ Ψ c + b c e • K e)
    (hK : ∀ c e, Ψ c ∘ₗ K e = K e ∘ₗ Ψ c) (hx : ∀ c, Ψ c x₀ = 0) {d : ℕ} (c : Fin d → C)
    (parent : V → Option V) (depth : V → ℕ)
    (hdepth : ∀ v w, parent v = some w → depth w < depth v) (σ τ : Fin d ≃ V)
    (hb : ∀ r e : Fin d, b (c r) e = forestIncidence parent (σ r) (τ e)) {y : M}
    (hy : switchProduct K d x₀ = y) :
    derivativeProduct Ψ c (switchProduct F d x₀) = y := by
  let : Fintype V := Fintype.ofEquiv (Fin d) σ
  refine derivativeProduct_switchProduct_eq_of_det_eq_one hF hK hx c ?_ hy
  have hmat : (Matrix.of fun r e : Fin d => b (c r) e) =
      (forestIncidence parent : Matrix V V R).submatrix σ τ := by
    ext r e
    simp [hb]
  rw [hmat, det_submatrix_equiv_charTwo, forestIncidence_det parent depth hdepth]

end ForestPairing

/-! ### The star selection at one rank -/

section Star

variable {r : ℕ} (main : Fin r → Prop) [DecidablePred main]

/-- The vertex of the incidence graph at one rank carried by the factor `l`. It is `none` when
the factor lies on the main component, which is the root, and otherwise it is the auxiliary
vertex `⟨l, h⟩` of the factor. -/
def vertexOf (l : Fin r) : Option {l : Fin r // ¬ main l} :=
  if h : main l then none else some ⟨l, h⟩

/-- The vertex of a factor on the main component is the root. -/
theorem vertexOf_of_main {l : Fin r} (h : main l) : vertexOf main l = none := by
  simp [vertexOf, h]

/-- The vertex of a factor off the main component is its own auxiliary vertex. -/
theorem vertexOf_of_not_main {l : Fin r} (h : ¬ main l) : vertexOf main l = some ⟨l, h⟩ := by
  simp [vertexOf, h]

/-- An auxiliary vertex is the vertex of its own factor. -/
theorem vertexOf_val (v : {l : Fin r // ¬ main l}) : vertexOf main v.val = some v :=
  vertexOf_of_not_main main v.2

/-- The first factor on the main component, which exists by the hypothesis `hmain`. -/
def firstMain (hmain : ∃ l, main l) : Fin r :=
  (Finset.univ.filter main).min' (by
    obtain ⟨l, hl⟩ := hmain
    exact ⟨l, by simp [hl]⟩)

/-- The first factor on the main component lies on the main component. -/
theorem firstMain_main (hmain : ∃ l, main l) : main (firstMain main hmain) :=
  (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter main) _)).2

variable [NeZero r]

/-- The star rule. The selected star edge attached to the auxiliary vertex `v` joins the centre
`0` to the factor `starEdgeLeaf main hmain v`. For an auxiliary vertex `v ≠ 0` this leaf is `v`
itself. If the centre `0` is auxiliary, the edge attached to it joins `0` to the first main
leaf. -/
def starEdgeLeaf (hmain : ∃ l, main l) (v : {l : Fin r // ¬ main l}) : Fin r :=
  if v.val = 0 then firstMain main hmain else v.val

/-- The leaf of the selected edge attached to an auxiliary vertex `v ≠ 0` is `v`. -/
theorem starEdgeLeaf_of_ne_zero (hmain : ∃ l, main l) {v : {l : Fin r // ¬ main l}}
    (hv : v.val ≠ 0) : starEdgeLeaf main hmain v = v.val := by
  simp [starEdgeLeaf, hv]

/-- The leaf of the selected edge attached to the auxiliary centre is the first main leaf. -/
theorem starEdgeLeaf_of_eq_zero (hmain : ∃ l, main l) {v : {l : Fin r // ¬ main l}}
    (hv : v.val = 0) : starEdgeLeaf main hmain v = firstMain main hmain := by
  simp [starEdgeLeaf, hv]

/-- Every selected edge is a star edge `(0, l)` with `l ≠ 0`. -/
theorem starEdgeLeaf_ne_zero (hmain : ∃ l, main l) (v : {l : Fin r // ¬ main l}) :
    starEdgeLeaf main hmain v ≠ 0 := by
  by_cases hv : v.val = 0
  · rw [starEdgeLeaf_of_eq_zero main hmain hv]
    intro h
    have h0 := firstMain_main main hmain
    rw [h, ← hv] at h0
    exact v.2 h0
  · rwa [starEdgeLeaf_of_ne_zero main hmain hv]

/-- Distinct auxiliary vertices carry distinct selected edges. -/
theorem starEdgeLeaf_injective (hmain : ∃ l, main l) :
    Function.Injective (starEdgeLeaf main hmain) := by
  have hfirst : ∀ v : {l : Fin r // ¬ main l}, firstMain main hmain ≠ v.val := fun v h =>
    v.2 (h ▸ firstMain_main main hmain)
  intro v w hvw
  by_cases hv : v.val = 0 <;> by_cases hw : w.val = 0
  · exact Subtype.ext (hv.trans hw.symm)
  · rw [starEdgeLeaf_of_eq_zero main hmain hv, starEdgeLeaf_of_ne_zero main hmain hw] at hvw
    exact absurd hvw (hfirst w)
  · rw [starEdgeLeaf_of_ne_zero main hmain hv, starEdgeLeaf_of_eq_zero main hmain hw] at hvw
    exact absurd hvw.symm (hfirst v)
  · rw [starEdgeLeaf_of_ne_zero main hmain hv, starEdgeLeaf_of_ne_zero main hmain hw] at hvw
    exact Subtype.ext hvw

/-- The reduced incidence matrix of the selected star edges at one rank. Its rows are the
auxiliary vertices and its columns are the selected edges, each indexed by the auxiliary vertex
to which it is attached. The entry in row `v` and column `e` counts the endpoints `0` and
`starEdgeLeaf main hmain e` of the edge whose vertex is `v`. -/
def starIncidence (R : Type*) [CommRing R] (hmain : ∃ l, main l) :
    Matrix {l : Fin r // ¬ main l} {l : Fin r // ¬ main l} R :=
  Matrix.of fun v e =>
    (if vertexOf main 0 = some v then 1 else 0) +
      if vertexOf main (starEdgeLeaf main hmain e) = some v then 1 else 0

/-- The parent function of the selected star forest. The auxiliary vertex of the centre, if it
exists, has the root as parent. Every other auxiliary vertex has the vertex of the centre as
parent, which is the root when the centre lies on the main component. -/
def starParent (v : {l : Fin r // ¬ main l}) : Option {l : Fin r // ¬ main l} :=
  if v.val = 0 then none else vertexOf main 0

/-- The depth function of the selected star forest. -/
def starDepth (v : {l : Fin r // ¬ main l}) : ℕ :=
  if v.val = 0 then 0 else 1

/-- The parent of a vertex of the selected star forest has smaller depth. -/
theorem starDepth_lt_of_starParent (v w : {l : Fin r // ¬ main l})
    (h : starParent main v = some w) : starDepth main w < starDepth main v := by
  by_cases hv : v.val = 0
  · simp [starParent, hv] at h
  · simp only [starParent, hv, if_false] at h
    have hw : w.val = 0 := by
      by_cases h0 : main 0
      · rw [vertexOf_of_main main h0] at h
        simp at h
      · rw [vertexOf_of_not_main main h0, Option.some_inj] at h
        rw [← h]
    simp [starDepth, hv, hw]

/-- The incidence matrix of the selected star edges is the reduced incidence matrix of the
forest given by `starParent`. -/
theorem starIncidence_eq_forestIncidence (R : Type*) [CommRing R] (hmain : ∃ l, main l) :
    starIncidence main R hmain = forestIncidence (starParent main) := by
  ext v e
  by_cases he : e.val = 0
  · have h0 : ¬ main 0 := he ▸ e.2
    have hve : (⟨0, h0⟩ : {l : Fin r // ¬ main l}) = e := Subtype.ext he.symm
    simp only [starIncidence, forestIncidence, Matrix.of_apply, starParent, he, ↓reduceIte,
      starEdgeLeaf_of_eq_zero main hmain he, vertexOf_of_main main (firstMain_main main hmain),
      vertexOf_of_not_main main h0, hve, Option.some_inj]
    by_cases hv : v = e
    · subst hv
      simp
    · simp [hv, Ne.symm hv]
  · simp only [starIncidence, forestIncidence, Matrix.of_apply, starParent, he, ↓reduceIte,
      starEdgeLeaf_of_ne_zero main hmain he, vertexOf_val, Option.some_inj]
    rw [add_comm]
    by_cases hv : v = e
    · subst hv
      simp
    · simp [hv, Ne.symm hv]

/-- **The selected star edges have incidence determinant one** over every commutative ring. -/
theorem det_starIncidence (R : Type*) [CommRing R] (hmain : ∃ l, main l) :
    (starIncidence main R hmain).det = 1 := by
  rw [starIncidence_eq_forestIncidence]
  exact forestIncidence_det (starParent main) (starDepth main) (starDepth_lt_of_starParent main)

/-- If the centre `0` lies on the main component, then the incidence matrix of the selected star
edges is the identity matrix. -/
theorem starIncidence_eq_one_of_main_zero (R : Type*) [CommRing R] (hmain : ∃ l, main l)
    (h0 : main 0) : starIncidence main R hmain = 1 := by
  rw [starIncidence_eq_forestIncidence]
  ext v e
  simp [forestIncidence, starParent, vertexOf_of_main main h0, Matrix.one_apply]

end Star

/-! ### The determinant pairing for the star selection -/

section StarPairing

variable {R M C : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]
variable {Ψ : C → M →ₗ[R] M} {F K : ℕ → M →ₗ[R] M} {b : C → ℕ → R} {x₀ : M}
variable {r : ℕ} [NeZero r] (main : Fin r → Prop) [DecidablePred main]

/-- **The determinant pairing for the star selection at one rank.** In characteristic two,
suppose that the colours `c q` and the maps `F e` are renamed by bijections `σ` and `τ` onto the
auxiliary vertices, so that `b (c q) e` is the entry of `starIncidence` in row `σ q` and column
`τ e`. If `K (d - 1) ∘ ⋯ ∘ K 0` sends `x₀` to `y`, then the product of the operators `Ψ (c q)`
sends `F (d - 1) ∘ ⋯ ∘ F 0` applied to `x₀` to `y`. -/
theorem derivativeProduct_switchProduct_eq_of_star
    (hF : ∀ c e, Ψ c ∘ₗ F e = F e ∘ₗ Ψ c + b c e • K e)
    (hK : ∀ c e, Ψ c ∘ₗ K e = K e ∘ₗ Ψ c) (hx : ∀ c, Ψ c x₀ = 0) {d : ℕ} (c : Fin d → C)
    (hmain : ∃ l, main l) (σ τ : Fin d ≃ {l : Fin r // ¬ main l})
    (hb : ∀ q e : Fin d, b (c q) e = starIncidence main R hmain (σ q) (τ e)) {y : M}
    (hy : switchProduct K d x₀ = y) :
    derivativeProduct Ψ c (switchProduct F d x₀) = y := by
  refine derivativeProduct_switchProduct_eq_of_forest hF hK hx c (starParent main)
    (starDepth main) (starDepth_lt_of_starParent main) σ τ (fun q e => ?_) hy
  rw [hb, starIncidence_eq_forestIncidence]

end StarPairing

end OnLeConjecture.KnotFloer
