/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidClosed
public import OnLeConjecture.KnotTheory.PositiveBraidGridWordModel
public import OnLeConjecture.KnotTheory.PositiveWordBraidEquiv
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# The closed braid of a positive word, and representation of closed braids by words

For a positive word `W` on `S` strands, the canonical smooth word path
`positiveGridWord W` of `KnotTheory.PositiveBraidGridWordModel` runs the letters of `W`
on the consecutive unit intervals `[j, j + 1]`, starting from the real configuration
`k ↦ k` and ending at the real configuration `k ↦ W.permutation⁻¹ k`. Over
`[0, length W + 1]` it is a closed braid with monodromy `W.permutation⁻¹`.

A closed braid `K` over `[u, v]` is *represented by* `W` if, after a relabelling of
its strands, it is isotopic through closed braids (`ClosedStrandBraidIsotopic`) to the
canonical closed braid of `W`, reparametrized affinely onto `[u, v]`. This is the
precise meaning of the phrase "the braid is represented, through closed braids, by
the word `W`" in job J14.

Representation determines the monodromy up to the relabelling and therefore the
number of permutation cycles of the word. It is invariant under isotopy, under
multiplication by nonzero constants, and under affine changes of the parameter.

The module also proves the concatenation formula of the canonical word path:
`positiveGridWord (u ++ v) k t` is the sum of the path of `u` at `t` and the path of `v`
at `t - length u`, the latter labelled after the permutation of `u`, minus the
common intermediate position.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### The canonical closed braid of a positive word -/

/-- The affine change of parameter from `[u, v]` onto `[0, length W + 1]`. -/
def positiveWordModelTime {S : ℕ} (W : PositiveAdjacentWord S) (u v t : ℝ) : ℝ :=
  (t - u) / (v - u) * ((W.length : ℝ) + 1)

/-- The canonical closed braid of `W`, parametrized by `[u, v]`. -/
def positiveWordModel {S : ℕ} (W : PositiveAdjacentWord S) (u v : ℝ) : Fin S → ℝ → ℂ :=
  fun k t => positiveGridWord W k (positiveWordModelTime W u v t)

theorem positiveGridWord_isClosedStrandBraid {S : ℕ} (W : PositiveAdjacentWord S) :
    IsClosedStrandBraid (positiveGridWord W) 0 ((W.length : ℝ) + 1) W.permutation⁻¹ where
  lt := by positivity
  continuousOn k := (positiveGridWord_contDiff W k).continuous.continuousOn
  injective t _ := positiveGridWord_injective W t
  closing k := by
    rw [positiveGridWord_of_length_le W k (by linarith), positiveGridWord_of_nonpos W _ le_rfl]
    rfl

theorem positiveWordModelTime_mapsTo {S : ℕ} (W : PositiveAdjacentWord S) {u v : ℝ}
    (huv : u < v) :
    MapsTo (positiveWordModelTime W u v) (Icc u v) (Icc 0 ((W.length : ℝ) + 1)) := by
  intro t ht
  have hd : 0 < v - u := sub_pos.mpr huv
  have hL : (0 : ℝ) < (W.length : ℝ) + 1 := by positivity
  unfold positiveWordModelTime
  constructor
  · exact mul_nonneg (div_nonneg (sub_nonneg.mpr ht.1) hd.le) hL.le
  · have h1 : (t - u) / (v - u) ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
    nlinarith

theorem positiveWordModelTime_left {S : ℕ} (W : PositiveAdjacentWord S) (u v : ℝ) :
    positiveWordModelTime W u v u = 0 := by
  simp [positiveWordModelTime]

theorem positiveWordModelTime_right {S : ℕ} (W : PositiveAdjacentWord S) {u v : ℝ}
    (huv : u < v) : positiveWordModelTime W u v v = (W.length : ℝ) + 1 := by
  have hd : v - u ≠ 0 := (sub_pos.mpr huv).ne'
  simp [positiveWordModelTime, div_self hd]

theorem positiveWordModelTime_continuous {S : ℕ} (W : PositiveAdjacentWord S) (u v : ℝ) :
    Continuous (positiveWordModelTime W u v) := by
  unfold positiveWordModelTime
  fun_prop

theorem positiveWordModel_isClosedStrandBraid {S : ℕ} (W : PositiveAdjacentWord S)
    {u v : ℝ} (huv : u < v) :
    IsClosedStrandBraid (positiveWordModel W u v) u v W.permutation⁻¹ :=
  (positiveGridWord_isClosedStrandBraid W).comp_time huv
    (positiveWordModelTime_continuous W u v).continuousOn (positiveWordModelTime_mapsTo W huv)
    (positiveWordModelTime_left W u v) (positiveWordModelTime_right W huv)

/-! ### Representation of a closed braid by a positive word -/

/-- The closed braid `K` over `[u, v]` is represented, through closed braids, by the
positive word `W`: after relabelling its strands by some permutation `π`, it is isotopic
through closed braids to the canonical closed braid of `W` parametrized by `[u, v]`. -/
def IsRepresentedByPositiveWord {S : ℕ} (K : Fin S → ℝ → ℂ) (u v : ℝ)
    (W : PositiveAdjacentWord S) : Prop :=
  ∃ π : Equiv.Perm (Fin S),
    ClosedStrandBraidIsotopic (fun k t => K (π k) t) (positiveWordModel W u v) u v
      W.permutation⁻¹

/-- The number of cycles of a permutation, including fixed points. -/
def permCycleCount {S : ℕ} (τ : Equiv.Perm (Fin S)) : ℕ := by
  classical
  exact Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid τ))

theorem permCycleCount_conj {S : ℕ} (τ g : Equiv.Perm (Fin S)) :
    permCycleCount (g * τ * g⁻¹) = permCycleCount τ := by
  classical
  unfold permCycleCount
  let e : Quotient (Equiv.Perm.SameCycle.setoid τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (g * τ * g⁻¹)) :=
    Quotient.congr g fun a b => by
      change τ.SameCycle a b ↔ (g * τ * g⁻¹).SameCycle (g a) (g b)
      rw [Equiv.Perm.sameCycle_conj]
      simp
  exact (Fintype.card_congr e).symm.trans (by convert rfl)

theorem permCycleCount_inv {S : ℕ} (τ : Equiv.Perm (Fin S)) :
    permCycleCount τ⁻¹ = permCycleCount τ := by
  classical
  unfold permCycleCount
  let e : Quotient (Equiv.Perm.SameCycle.setoid τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid τ⁻¹) :=
    Quotient.congr (Equiv.refl _) fun a b => by
      change τ.SameCycle a b ↔ τ⁻¹.SameCycle a b
      rw [Equiv.Perm.sameCycle_inv]
  exact (Fintype.card_congr e).symm.trans (by convert rfl)

theorem SignedAdjacentWord.cycleCount_eq_permCycleCount {S : ℕ} (w : SignedAdjacentWord S) :
    w.cycleCount = permCycleCount w.permutation := by
  classical
  unfold SignedAdjacentWord.cycleCount permCycleCount
  convert rfl

namespace IsRepresentedByPositiveWord

variable {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ} {W : PositiveAdjacentWord S}

/-- Representation identifies the monodromy with the inverse word permutation, up to the
relabelling. -/
theorem monodromy_conj {τ : Equiv.Perm (Fin S)} (hK : IsClosedStrandBraid K u v τ)
    {π : Equiv.Perm (Fin S)}
    (hπ : ClosedStrandBraidIsotopic (fun k t => K (π k) t) (positiveWordModel W u v) u v
      W.permutation⁻¹) :
    π⁻¹ * τ * π = W.permutation⁻¹ :=
  (hK.relabel π).monodromy_unique hπ.left

/-- The monodromy of a represented closed braid is conjugate to the inverse word
permutation. -/
theorem exists_monodromy_conj {τ : Equiv.Perm (Fin S)} (hK : IsClosedStrandBraid K u v τ)
    (h : IsRepresentedByPositiveWord K u v W) :
    ∃ π : Equiv.Perm (Fin S), π⁻¹ * τ * π = W.permutation⁻¹ := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, monodromy_conj hK hπ⟩

/-- The cycles of a represented closed braid are the cycles of its word. -/
theorem cycleCount_eq {τ : Equiv.Perm (Fin S)} (hK : IsClosedStrandBraid K u v τ)
    (h : IsRepresentedByPositiveWord K u v W) :
    W.toSigned.cycleCount = permCycleCount τ := by
  obtain ⟨π, hπ⟩ := exists_monodromy_conj hK h
  rw [SignedAdjacentWord.cycleCount_eq_permCycleCount]
  change permCycleCount W.permutation = _
  rw [← permCycleCount_inv W.permutation, ← hπ]
  have he : π⁻¹ * τ * π = π⁻¹ * τ * π⁻¹⁻¹ := by rw [inv_inv]
  rw [he, permCycleCount_conj]

/-- Representation is invariant under isotopy through closed braids. -/
theorem of_isotopic {τ : Equiv.Perm (Fin S)} {K' : Fin S → ℝ → ℂ}
    (h : IsRepresentedByPositiveWord K' u v W) (hKK' : ClosedStrandBraidIsotopic K K' u v τ) :
    IsRepresentedByPositiveWord K u v W := by
  obtain ⟨π, hπ⟩ := h
  have hconj := monodromy_conj hKK'.right hπ
  refine ⟨π, ?_⟩
  have hrel := hKK'.relabel π
  rw [hconj] at hrel
  exact hrel.trans hπ

/-- Representation is invariant under multiplication by a nonzero constant. -/
theorem const_mul {τ : Equiv.Perm (Fin S)} (hK : IsClosedStrandBraid K u v τ)
    (h : IsRepresentedByPositiveWord K u v W) {c : ℂ} (hc : c ≠ 0) :
    IsRepresentedByPositiveWord (fun k t => c * K k t) u v W := by
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hK' : IsClosedStrandBraid (fun k t => c * K k t) u v τ :=
    ⟨hK.lt, fun k => continuousOn_const.mul (hK.continuousOn k),
      fun t ht k l hkl => hK.injective t ht (mul_left_cancel₀ hc hkl),
      fun k => by simp only [hK.closing k]⟩
  refine of_isotopic (τ := τ) h ?_
  have hiso := ClosedStrandBraidIsotopic.const_mul hK' hc'
  refine (hiso.congr (fun k t _ => rfl) (fun k t _ => ?_))
  simp [inv_mul_cancel_left₀ hc]

/-- Representation is invariant under an increasing affine change of parameter. -/
theorem comp_affine (h : IsRepresentedByPositiveWord K u v W) {u' v' : ℝ} (huv' : u' < v') :
    IsRepresentedByPositiveWord
      (fun k t => K k (u + (t - u') / (v' - u') * (v - u))) u' v' W := by
  obtain ⟨π, hπ⟩ := h
  have huv : u < v := hπ.left.lt
  let φ : ℝ → ℝ := fun t => u + (t - u') / (v' - u') * (v - u)
  have hd' : 0 < v' - u' := sub_pos.mpr huv'
  have hd : 0 < v - u := sub_pos.mpr huv
  have hφc : Continuous φ := by fun_prop
  have hφm : MapsTo φ (Icc u' v') (Icc u v) := by
    intro t ht
    have h0 : 0 ≤ (t - u') / (v' - u') := div_nonneg (sub_nonneg.mpr ht.1) hd'.le
    have h1 : (t - u') / (v' - u') ≤ 1 := (div_le_one hd').mpr (by linarith [ht.2])
    constructor <;> nlinarith
  have hφu : φ u' = u := by simp [φ]
  have hφv : φ v' = v := by simp [φ, div_self hd'.ne']
  refine ⟨π, (hπ.comp_time huv' hφc.continuousOn hφm hφu hφv).congr (fun k t _ => rfl) ?_⟩
  intro k t _
  simp only [positiveWordModel, positiveWordModelTime, φ]
  congr 1
  field_simp
  ring

end IsRepresentedByPositiveWord

/-! ### Concatenation of canonical word paths -/

theorem positiveWordPrefix_append_of_le {S : ℕ} (u v : PositiveAdjacentWord S) {j : ℕ}
    (hj : j ≤ u.length) : positiveWordPrefix (u ++ v) j = positiveWordPrefix u j := by
  simp [positiveWordPrefix, List.take_append_of_le_length hj]

theorem positiveWordPrefix_append_length_add {S : ℕ} (u v : PositiveAdjacentWord S) (j : ℕ) :
    positiveWordPrefix (u ++ v) (u.length + j) = u.permutation * positiveWordPrefix v j := by
  rw [positiveWordPrefix, List.take_length_add_append,
    PositiveAdjacentWord.permutation_append_eq_mul]
  rfl

theorem perm_mul_symm_apply {S : ℕ} (σ ρ : Equiv.Perm (Fin S)) (k : Fin S) :
    (σ * ρ).symm k = ρ.symm (σ.symm k) := by
  simp [Equiv.Perm.mul_def]

theorem positiveWordReal_append {S : ℕ} (u v : PositiveAdjacentWord S) (k : Fin S) (t : ℝ) :
    positiveWordReal (u ++ v) k t = positiveWordReal u k t +
      positiveWordReal v (u.permutation.symm k) (t - u.length) -
      ((u.permutation.symm k).val : ℝ) := by
  unfold positiveWordReal
  rw [List.length_append, Finset.sum_range_add]
  have h1 : ∀ j ∈ Finset.range u.length,
      Real.smoothTransition (t - j) *
          ((((positiveWordPrefix (u ++ v) (j + 1)).symm k).val : ℝ) -
            (((positiveWordPrefix (u ++ v) j).symm k).val : ℝ)) =
        Real.smoothTransition (t - j) *
          ((((positiveWordPrefix u (j + 1)).symm k).val : ℝ) -
            (((positiveWordPrefix u j).symm k).val : ℝ)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [positiveWordPrefix_append_of_le u v (by omega),
      positiveWordPrefix_append_of_le u v (by omega)]
  have h2 : ∀ j ∈ Finset.range v.length,
      Real.smoothTransition (t - ((u.length + j : ℕ) : ℝ)) *
          ((((positiveWordPrefix (u ++ v) (u.length + j + 1)).symm k).val : ℝ) -
            (((positiveWordPrefix (u ++ v) (u.length + j)).symm k).val : ℝ)) =
        Real.smoothTransition (t - u.length - j) *
          ((((positiveWordPrefix v (j + 1)).symm (u.permutation.symm k)).val : ℝ) -
            (((positiveWordPrefix v j).symm (u.permutation.symm k)).val : ℝ)) := by
    intro j _
    rw [show u.length + j + 1 = u.length + (j + 1) by ring,
      positiveWordPrefix_append_length_add, positiveWordPrefix_append_length_add,
      perm_mul_symm_apply, perm_mul_symm_apply]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  ring

/-- The imaginary coordinate of the canonical word path as a sum over `range`. -/
theorem positiveGridWordImaginary_eq_sum_range {S : ℕ} (W : PositiveAdjacentWord S)
    (k : Fin S) (t : ℝ) :
    positiveGridWordImaginary W k t = ∑ j ∈ Finset.range W.length,
      (W[j]?).elim 0 fun i =>
        positiveGridGeneratorImaginary i ((positiveWordPrefix W j).symm k) (t - j) := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold positiveGridWordImaginary
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.getElem?_eq_getElem j.isLt]
  rfl

theorem positiveGridWordImaginary_append {S : ℕ} (u v : PositiveAdjacentWord S) (k : Fin S)
    (t : ℝ) :
    positiveGridWordImaginary (u ++ v) k t = positiveGridWordImaginary u k t +
      positiveGridWordImaginary v (u.permutation.symm k) (t - u.length) := by
  rw [positiveGridWordImaginary_eq_sum_range, positiveGridWordImaginary_eq_sum_range,
    positiveGridWordImaginary_eq_sum_range, List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [List.getElem?_append_left hj', positiveWordPrefix_append_of_le u v hj'.le]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      positiveWordPrefix_append_length_add, perm_mul_symm_apply]
    congr 1
    funext i
    congr 1
    push_cast
    ring

/-- The concatenation formula of canonical word paths. -/
theorem positiveGridWord_append {S : ℕ} (u v : PositiveAdjacentWord S) (k : Fin S) (t : ℝ) :
    positiveGridWord (u ++ v) k t = positiveGridWord u k t +
      positiveGridWord v (u.permutation.symm k) (t - u.length) -
      ((u.permutation.symm k).val : ℂ) := by
  apply Complex.ext
  · simp only [positiveGridWord_re, Complex.add_re, Complex.sub_re, Complex.natCast_re,
      positiveWordReal_append]
  · simp only [positiveGridWord_im, Complex.add_im, Complex.sub_im, Complex.natCast_im,
      sub_zero, positiveGridWordImaginary_append]

/-- Before the end of the first word, the concatenated path is the first path. -/
theorem positiveGridWord_append_of_le {S : ℕ} (u v : PositiveAdjacentWord S) (k : Fin S)
    {t : ℝ} (ht : t ≤ u.length) : positiveGridWord (u ++ v) k t = positiveGridWord u k t := by
  rw [positiveGridWord_append, positiveGridWord_of_nonpos v _ (by linarith)]
  ring

/-- After the end of the first word, the concatenated path is the second path, labelled
after the permutation of the first word. -/
theorem positiveGridWord_append_of_ge {S : ℕ} (u v : PositiveAdjacentWord S) (k : Fin S)
    {t : ℝ} (ht : (u.length : ℝ) ≤ t) :
    positiveGridWord (u ++ v) k t = positiveGridWord v (u.permutation.symm k) (t - u.length) := by
  rw [positiveGridWord_append, positiveGridWord_of_length_le u k ht]
  ring

/-- The canonical path is constant before time `0` and after the word length. -/
theorem positiveGridWord_eq_clamp {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) (t : ℝ) :
    positiveGridWord W k t = positiveGridWord W k (max 0 (min t W.length)) := by
  rcases le_or_gt t 0 with h | h
  · rw [positiveGridWord_of_nonpos W k h, positiveGridWord_of_nonpos W k
      (by simp only [max_le_iff, le_refl, true_and]; exact min_le_of_left_le h)]
  · rcases le_or_gt (W.length : ℝ) t with h' | h'
    · rw [positiveGridWord_of_length_le W k h', min_eq_right h',
        max_eq_right (by positivity), positiveGridWord_of_length_le W k le_rfl]
    · rw [min_eq_left h'.le, max_eq_right h.le]

end OnLeConjecture.Analytic
