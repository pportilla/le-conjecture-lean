/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.BraidMonodromyLayered
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Basic

/-!
# Local braid words between nearby configurations

A configuration of `S` labelled points of `ℂ` is a function `x : Fin S → ℂ`. This module attaches
a signed braid word to two nearby configurations, without any genericity assumption.

* `configSort x` is the permutation listing the labels of `x` by position, in the
  lexicographic order of `(Re, Im)` (`lexKey`). For a configuration with distinct real parts this
  is the order of the real parts. The lexicographic order breaks the ties of the real parts, so
  that no transversality assumption is needed.
* `localWord z x y` is the transition word between the orders of `x` and `y` of the layered
  words (`KnotTheory/BraidMonodromyLayered.lean`) whose heights are the points of the *center*
  `z`, ordered by `(Im, Re)` (`heightKey`).

The main results:

* `localWord_center`: if the points of the centers `z` and `z'` are pairwise at distance at least
  `m > 0`, and `x`, `y` lie within `m / 8` of both centers (pointwise), then
  `localWord z x y` and `localWord z' x y` are related by `SignedBraidEquiv`. The pairs whose
  orders differ between `x` and `y` have real parts within `m / 4`, hence imaginary parts
  at least `m / 2` apart, with the same sign for both centers.
* `localWord_comp`: `localWord z x y · localWord z y w ≡ localWord z x w`.
* `localWord_relabel`: the local word does not depend on the labelling of the points.
* `localWord_of_configSort_eq` and `localWord_of_configSort_swap`: if the orders of `x` and `y`
  agree, the local word is trivial; if they differ by the exchange of the positions `i` and
  `i + 1`, the local word is the single letter `σ_i^{±1}`, with sign `+1` exactly when the strand
  moving to the left is the higher one in the center.
-/

@[expose] public noncomputable section

open Function

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### Keys and sorting -/

/-- The lexicographic key `(Re z, Im z)` of a complex number. -/
def lexKey (z : ℂ) : Lex (ℝ × ℝ) := toLex (z.re, z.im)

/-- The height key `(Im z, Re z)` of a complex number. -/
def heightKey (z : ℂ) : Lex (ℝ × ℝ) := toLex (z.im, z.re)

theorem lexKey_injective : Injective lexKey := by
  intro z w h
  simp only [lexKey, toLex_inj, Prod.mk.injEq] at h
  exact Complex.ext h.1 h.2

theorem heightKey_injective : Injective heightKey := by
  intro z w h
  simp only [heightKey, toLex_inj, Prod.mk.injEq] at h
  exact Complex.ext h.2 h.1

theorem lexKey_lt_iff (z w : ℂ) :
    lexKey z < lexKey w ↔ z.re < w.re ∨ z.re = w.re ∧ z.im < w.im :=
  Prod.Lex.toLex_lt_toLex

theorem heightKey_lt_iff (z w : ℂ) :
    heightKey z < heightKey w ↔ z.im < w.im ∨ z.im = w.im ∧ z.re < w.re :=
  Prod.Lex.toLex_lt_toLex

theorem re_le_of_lexKey_lt {z w : ℂ} (h : lexKey z < lexKey w) : z.re ≤ w.re := by
  rcases (lexKey_lt_iff z w).mp h with h | h
  · exact h.le
  · exact h.1.le

/-- The labels of a configuration listed by position, in the lexicographic order of
`(Re, Im)`. -/
def configSort {S : ℕ} (x : Fin S → ℂ) : Equiv.Perm (Fin S) := Tuple.sort (lexKey ∘ x)

theorem configSort_strictMono {S : ℕ} {x : Fin S → ℂ} (hx : Injective x) :
    StrictMono fun j => lexKey (x (configSort x j)) :=
  (Tuple.monotone_sort (lexKey ∘ x)).strictMono_of_injective
    ((lexKey_injective.comp hx).comp (Tuple.sort (lexKey ∘ x)).injective)

/-- The sorting permutation is characterized by strict monotonicity of the keys. -/
theorem eq_configSort {S : ℕ} {x : Fin S → ℂ} (hx : Injective x) {σ : Equiv.Perm (Fin S)}
    (hσ : StrictMono fun j => lexKey (x (σ j))) : σ = configSort x := by
  rw [configSort, Tuple.eq_sort_iff]
  refine ⟨hσ.monotone, fun i j hij he => ?_⟩
  exact absurd (σ.injective (hx (lexKey_injective he))) hij.ne

/-- Positions in the sorted order compare as the keys of the labels. -/
theorem configSort_symm_lt_iff {S : ℕ} {x : Fin S → ℂ} (hx : Injective x) (k l : Fin S) :
    (configSort x).symm k < (configSort x).symm l ↔ lexKey (x k) < lexKey (x l) := by
  have h := (configSort_strictMono hx).lt_iff_lt (a := (configSort x).symm k)
    (b := (configSort x).symm l)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Relabelling the points by `τ` changes the sorting permutation by `τ⁻¹`. -/
theorem configSort_comp {S : ℕ} {x : Fin S → ℂ} (hx : Injective x) (τ : Equiv.Perm (Fin S)) :
    configSort (x ∘ τ) = τ⁻¹ * configSort x := by
  symm
  apply eq_configSort (hx.comp τ.injective)
  intro i j hij
  simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  exact configSort_strictMono hx hij

/-! ### Separation and closeness -/

/-- The points of `z` are pairwise at distance at least `m`. -/
def ConfigSeparated {S : ℕ} (z : Fin S → ℂ) (m : ℝ) : Prop :=
  ∀ k l, k ≠ l → m ≤ ‖z k - z l‖

/-- Each point of `x` is within `ε` of the point of `y` with the same label. -/
def ConfigNear {S : ℕ} (x y : Fin S → ℂ) (ε : ℝ) : Prop :=
  ∀ k, ‖x k - y k‖ < ε

theorem ConfigSeparated.injective {S : ℕ} {z : Fin S → ℂ} {m : ℝ} (hz : ConfigSeparated z m)
    (hm : 0 < m) : Injective z := by
  intro k l h
  by_contra hkl
  have := hz k l hkl
  rw [h, sub_self, norm_zero] at this
  linarith

theorem ConfigNear.symm {S : ℕ} {x y : Fin S → ℂ} {ε : ℝ} (h : ConfigNear x y ε) :
    ConfigNear y x ε := fun k => by rw [norm_sub_rev]; exact h k

theorem ConfigNear.mono {S : ℕ} {x y : Fin S → ℂ} {ε ε' : ℝ} (h : ConfigNear x y ε)
    (hε : ε ≤ ε') : ConfigNear x y ε' := fun k => (h k).trans_le hε

theorem ConfigNear.trans {S : ℕ} {x y w : Fin S → ℂ} {ε ε' : ℝ} (h : ConfigNear x y ε)
    (h' : ConfigNear y w ε') : ConfigNear x w (ε + ε') := fun k =>
  calc ‖x k - w k‖ = ‖(x k - y k) + (y k - w k)‖ := by ring_nf
    _ ≤ ‖x k - y k‖ + ‖y k - w k‖ := norm_add_le _ _
    _ < ε + ε' := add_lt_add (h k) (h' k)

theorem ConfigNear.comp {S : ℕ} {x y : Fin S → ℂ} {ε : ℝ} (h : ConfigNear x y ε)
    (τ : Equiv.Perm (Fin S)) : ConfigNear (x ∘ τ) (y ∘ τ) ε := fun k => h (τ k)

theorem ConfigSeparated.comp {S : ℕ} {z : Fin S → ℂ} {m : ℝ} (h : ConfigSeparated z m)
    (τ : Equiv.Perm (Fin S)) : ConfigSeparated (z ∘ τ) m :=
  fun k l hkl => h (τ k) (τ l) (τ.injective.ne hkl)

/-- A separated configuration stays injective after a perturbation by less than half the
separation. -/
theorem ConfigSeparated.injective_of_near {S : ℕ} {z x : Fin S → ℂ} {m : ℝ}
    (hz : ConfigSeparated z m) (hx : ConfigNear x z (m / 2)) : Injective x := by
  intro k l h
  by_contra hkl
  have h1 := hz k l hkl
  have h2 : ‖z k - z l‖ ≤ ‖x k - z k‖ + ‖x l - z l‖ := by
    calc ‖z k - z l‖ = ‖(x l - z l) - (x k - z k)‖ := by rw [h]; ring_nf
      _ ≤ ‖x l - z l‖ + ‖x k - z k‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  linarith [hx k, hx l]

/-- If two points of a separated configuration have real parts within `m / 4`, their
imaginary parts are more than `m / 2` apart. -/
theorem abs_im_sub_gt_of_abs_re_sub_lt {m : ℝ} (hm : 0 < m) {a b : ℂ} (hsep : m ≤ ‖a - b‖)
    (hre : |(a - b).re| < m / 4) : m / 2 < |(a - b).im| := by
  have hsq : ‖a - b‖ ^ 2 = (a - b).re ^ 2 + (a - b).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : m ^ 2 ≤ ‖a - b‖ ^ 2 := by
    have := norm_nonneg (a - b)
    nlinarith
  have h2 : (a - b).re ^ 2 < (m / 4) ^ 2 := by
    have := abs_nonneg (a - b).re
    rw [← sq_abs]
    nlinarith
  have h3 : (m / 2) ^ 2 < |(a - b).im| ^ 2 := by
    rw [sq_abs]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h3

/-! ### Local words -/

/-- **The local word** from the configuration `x` to the configuration `y` with center `z`:
the transition word between the orders of `x` and `y` of the layered words whose heights are
the height keys of the points of `z`. -/
def localWord {S : ℕ} (z x y : Fin S → ℂ) : SignedAdjacentWord S :=
  SignedAdjacentWord.inv (layeredWord S (heightKey ∘ z ∘ ⇑(configSort x))) ++
    layeredWord S (heightKey ∘ z ∘ ⇑(configSort y))

/-- The local words with a common center compose. -/
theorem localWord_comp {S : ℕ} (z x y w : Fin S → ℂ) :
    SignedBraidEquiv (localWord z x y ++ localWord z y w) (localWord z x w) := by
  unfold localWord
  exact SignedBraidEquiv.transition_comp _ _ _

/-- The local word from a configuration to itself is trivial. -/
theorem localWord_self {S : ℕ} (z x : Fin S → ℂ) : SignedBraidEquiv (localWord z x x) [] :=
  SignedBraidEquiv.inv_append_self _

/-- The local word does not depend on the labelling of the points. -/
theorem localWord_relabel {S : ℕ} {z x y : Fin S → ℂ} (hx : Injective x) (hy : Injective y)
    (τ : Equiv.Perm (Fin S)) : localWord (z ∘ τ) (x ∘ τ) (y ∘ τ) = localWord z x y := by
  unfold localWord
  rw [configSort_comp hx, configSort_comp hy]
  congr 3 <;> funext j <;> simp

/-- If the orders of `x` and `y` agree, the local word is trivial. -/
theorem localWord_of_configSort_eq {S : ℕ} (z : Fin S → ℂ) {x y : Fin S → ℂ}
    (h : configSort x = configSort y) : SignedBraidEquiv (localWord z x y) [] := by
  unfold localWord
  rw [h]
  exact SignedBraidEquiv.inv_append_self _

/-- If the orders of `x` and `y` differ by the exchange of the positions `i` and `i + 1`, the
local word is the single letter `σ_i^{ε}`, where `ε = +1` exactly when the strand at position
`i + 1` of `x` (which moves to the left) is higher in the center than the strand at position
`i`. -/
theorem localWord_of_configSort_swap {n : ℕ} {z : Fin (n + 1) → ℂ} (hz : Injective z)
    {x y : Fin (n + 1) → ℂ} (i : Fin n)
    (h : configSort y = configSort x * adjacentSwap (m := n + 1) i) :
    SignedBraidEquiv (localWord z x y)
      ([(i, exchangeSign (heightKey (z (configSort x (adjacentLower (m := n + 1) i))))
        (heightKey (z (configSort x (adjacentUpper (m := n + 1) i)))))] :
          SignedAdjacentWord (n + 1)) := by
  unfold localWord
  rw [h]
  exact layeredTransition_swap (c := heightKey ∘ z) (heightKey_injective.comp hz) _ i

/-- The pairs whose order differs between two configurations near a common center have
nearly equal real parts. -/
theorem abs_re_sub_lt_of_order_change {S : ℕ} {z x y : Fin S → ℂ} {ε : ℝ}
    (hxz : ConfigNear x z ε) (hyz : ConfigNear y z ε) {k l : Fin S}
    (hx : lexKey (x k) < lexKey (x l)) (hy : lexKey (y l) < lexKey (y k)) :
    |(z k - z l).re| < 2 * ε := by
  have h1 := re_le_of_lexKey_lt hx
  have h2 := re_le_of_lexKey_lt hy
  have e1 := (Complex.abs_re_le_norm (x k - z k)).trans_lt (hxz k)
  have e2 := (Complex.abs_re_le_norm (x l - z l)).trans_lt (hxz l)
  have e3 := (Complex.abs_re_le_norm (y k - z k)).trans_lt (hyz k)
  have e4 := (Complex.abs_re_le_norm (y l - z l)).trans_lt (hyz l)
  simp only [Complex.sub_re] at e1 e2 e3 e4 ⊢
  rw [abs_lt] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-- **Independence of the center.** If the points of the centers `z` and `z'` are pairwise at
distance at least `m > 0` and `x`, `y` lie within `m / 8` of both centers, the two local words
from `x` to `y` are related by `SignedBraidEquiv`. -/
theorem localWord_center {S : ℕ} {m : ℝ} (hm : 0 < m) {z z' x y : Fin S → ℂ}
    (hz : ConfigSeparated z m) (hz' : ConfigSeparated z' m)
    (hxz : ConfigNear x z (m / 8)) (hyz : ConfigNear y z (m / 8))
    (hxz' : ConfigNear x z' (m / 8)) (hyz' : ConfigNear y z' (m / 8)) :
    SignedBraidEquiv (localWord z x y) (localWord z' x y) := by
  rcases S with _ | n
  · have h1 : localWord z x y = [] := by
      rcases localWord z x y with _ | ⟨a, _⟩
      · rfl
      · exact a.1.elim0
    have h2 : localWord z' x y = [] := by
      rcases localWord z' x y with _ | ⟨a, _⟩
      · rfl
      · exact a.1.elim0
    rw [h1, h2]
    exact SignedBraidEquiv.refl _
  have hinjx : Injective x := hz.injective_of_near (hxz.mono (by linarith))
  have hinjy : Injective y := hz.injective_of_near (hyz.mono (by linarith))
  unfold localWord
  apply layeredTransition_congr (heightKey_injective.comp (hz.injective hm))
    (heightKey_injective.comp (hz'.injective hm))
  intro k l hkl hlk
  rw [configSort_symm_lt_iff hinjx] at hkl
  rw [configSort_symm_lt_iff hinjy] at hlk
  have hne : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
  have hre := abs_re_sub_lt_of_order_change hxz hyz hkl hlk
  have hre' := abs_re_sub_lt_of_order_change hxz' hyz' hkl hlk
  have him := abs_im_sub_gt_of_abs_re_sub_lt hm (hz k l hne) (by linarith)
  have him' := abs_im_sub_gt_of_abs_re_sub_lt hm (hz' k l hne) (by linarith)
  -- The two centers are within `m / 4` of each other.
  have hzz : ConfigNear z z' (m / 8 + m / 8) := hxz.symm.trans hxz'
  have d1 := (Complex.abs_im_le_norm (z k - z' k)).trans_lt (hzz k)
  have d2 := (Complex.abs_im_le_norm (z l - z' l)).trans_lt (hzz l)
  simp only [Complex.sub_im] at d1 d2 him him'
  simp only [Function.comp_apply, heightKey_lt_iff]
  rw [abs_lt] at d1 d2
  rcases lt_abs.mp him with h | h <;> rcases lt_abs.mp him' with h' | h'
  · -- both differences positive
    constructor
    · rintro (h1 | ⟨h1, -⟩) <;> linarith
    · rintro (h1 | ⟨h1, -⟩) <;> linarith
  · exfalso; linarith [d1.1, d1.2, d2.1, d2.2]
  · exfalso; linarith [d1.1, d1.2, d2.1, d2.2]
  · constructor
    · intro _; left; linarith
    · intro _; left; linarith

end OnLeConjecture.Analytic
