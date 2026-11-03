/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidSheets
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms

/-!
# The positive event word of the strict-transform sheets

For sheet data `D : MultiSheetData S` and a fibre rotation `c` separating the distinct
constant terms of the sheets, this module constructs one positive word `v`, the event word
of the strict-transform braid `D.strict c r₁` at a reference radius `r₁` and a regular
base angle, and proves:

* the strict-transform braid is represented by `v` at every small radius and every base
  angle (`IsRepresentedByPositiveWord`);
* the number of permutation cycles of `v` is the number of cycles of the monodromy `τ`;
* at every small radius and every regular base angle, the root braid `D.root 1 r` admits
  projected crossing data `SheetCrossingData` for the projection `Re (c ·)`, all of whose
  crossings are positive, with signed crossing count equal to the exponent sum of
  `fullTwistWord S ++ v`.

The last statement is the hypothesis `hword` of the J15 theorem
`fullTwistWord_append_length_of_rootBraid`, at the level of sheets. It is proved through
the factorization of the strand discriminant of the root braid as `ξ^{S(S-1)}` times the
strand discriminant of the strict-transform braid, the winding invariance of strand
discriminants under isotopy through closed braids, and the pair count of
`SheetCrossingData`.
-/

@[expose] public noncomputable section

open Set Filter Metric Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Crossing data with only positive crossings, for strands `θ ↦ c y_k(θ)` with finitely
many positive transverse projected crossings and regular endpoints. -/
theorem exists_positive_sheetCrossingData {m : ℕ} {y : Fin m → ℝ → ℂ} {c : ℂ} {b : ℝ}
    (hdiff : ∀ k, Differentiable ℝ (y k))
    (hfin : {θ | θ ∈ Icc b (b + 2 * π) ∧ ∃ k l, k ≠ l ∧ (c * y k θ).re = (c * y l θ).re}.Finite)
    (hb : ∀ k l, k ≠ l → (c * y k b).re ≠ (c * y l b).re)
    (hd : ∀ k l, k ≠ l → (c * y k (b + 2 * π)).re ≠ (c * y l (b + 2 * π)).re)
    (hpos : ∀ θ k l, k ≠ l → (c * y k θ).re = (c * y l θ).re →
      0 < -deriv (fun t => (c * y k t - c * y l t).re) θ * (c * y k θ - c * y l θ).im) :
    ∃ D : SheetCrossingData m y b c,
      (∀ k l, k < l → ∀ θ ∈ D.crossings k l, D.crossingSign k l θ = 1) ∧
      (∀ k l, k < l → ∀ θ, θ ∈ D.crossings k l ↔
        θ ∈ Icc b (b + 2 * π) ∧ (c * y k θ).re = (c * y l θ).re) := by
  have hsub (k l : Fin m) (θ : ℝ) : (c * (y k θ - y l θ)).re = 0 ↔
      (c * y k θ).re = (c * y l θ).re := by
    rw [mul_sub, Complex.sub_re, sub_eq_zero]
  have hderiv (k l : Fin m) (θ : ℝ) :
      deriv (fun t => (c * y k t - c * y l t).re) θ =
        (c * deriv (fun t => y k t - y l t) θ).re := by
    have hd : DifferentiableAt ℝ (fun t => y k t - y l t) θ := ((hdiff k).sub (hdiff l)) θ
    have hfun : (fun t => (c * y k t - c * y l t).re) =
        fun t => ((fun t => c * (y k t - y l t)) t).re := by
      funext t
      ring_nf
    rw [hfun, deriv_re_eq_re_deriv (hd.const_mul c), deriv_const_mul c hd]
  have htr : ∀ k l, k ≠ l → ∀ θ, (c * (y k θ - y l θ)).re = 0 →
      (c * deriv (fun t => y k t - y l t) θ).re ≠ 0 := by
    intro k l hkl θ h0 hz
    have h := hpos θ k l hkl ((hsub k l θ).mp h0)
    rw [hderiv, hz, neg_zero, zero_mul] at h
    exact lt_irrefl _ h
  let D := sheetCrossingDataOfTransverse y b c hdiff
    (fun k l hkl => hfin.subset fun θ hθ => ⟨hθ.1, k, l, hkl, (hsub k l θ).mp hθ.2⟩)
    (fun k l hkl h => hb k l hkl ((hsub k l b).mp h))
    (fun k l hkl h => hd k l hkl ((hsub k l _).mp h)) htr
  have hmem : ∀ k l, k < l → ∀ θ, θ ∈ D.crossings k l ↔
      θ ∈ Icc b (b + 2 * π) ∧ (c * y k θ).re = (c * y l θ).re := by
    intro k l hkl θ
    constructor
    · intro hθ
      have hI : θ ∈ Icc b (b + 2 * π) := Ioo_subset_Icc_self (D.crossings_subset k l hkl θ hθ)
      exact ⟨hI, (hsub k l θ).mp ((D.mem_crossings_iff k l hkl θ hI).mpr hθ)⟩
    · rintro ⟨hI, h⟩
      exact (D.mem_crossings_iff k l hkl θ hI).mp ((hsub k l θ).mpr h)
  refine ⟨D, fun k l hkl θ hθ => ?_, hmem⟩
  have h := hpos θ k l hkl.ne ((hmem k l hkl θ).mp hθ).2
  rw [hderiv] at h
  apply SheetCrossingData.crossingSign_eq_one
  have heq : D.derivative k l θ = deriv (fun t => y k t - y l t) θ := rfl
  rw [heq, mul_sub]
  linarith

/-- With only positive crossings, the signed crossing count is the length of the
concatenated event word. -/
theorem SheetCrossingData.signedCount_eq_length {m : ℕ} {y : Fin m → ℝ → ℂ} {c : ℂ} {b : ℝ}
    (D : SheetCrossingData m y b c)
    (hsign : ∀ k l, k < l → ∀ θ ∈ D.crossings k l, D.crossingSign k l θ = 1)
    (hmem : ∀ k l, k < l → ∀ θ, θ ∈ D.crossings k l ↔
      θ ∈ Icc b (b + 2 * π) ∧ (c * y k θ).re = (c * y l θ).re)
    {N : ℕ} (event : Fin N → ℝ) (hev : StrictMono event)
    (hevI : ∀ j, event j ∈ Icc b (b + 2 * π))
    (hcover : ∀ θ ∈ Icc b (b + 2 * π),
      (∃ k l, k ≠ l ∧ (c * y k θ).re = (c * y l θ).re) → ∃ j, event j = θ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hw : ∀ j, IsPositiveBraidEventWord (fun k θ => c * y k θ) (event j) (σ j.castSucc)
      (σ j.succ) (w j)) :
    D.signedCount = (List.ofFn w).flatten.length := by
  classical
  have h := D.exponentSum_flatten_eq_signedCount event hev.injective
    (fun k l hkl θ hθ => hcover θ ((hmem k l hkl θ).mp hθ).1
      ⟨k, l, hkl.ne, ((hmem k l hkl θ).mp hθ).2⟩)
    (fun j => (w j).toSigned) (fun j => by
      rw [PositiveAdjacentWord.exponentSum_toSigned, (hw j).length_eq_card_labels]
      have hfilter : ((Finset.univ : Finset (Fin m × Fin m)).filter
          fun p => p.1 < p.2 ∧ event j ∈ D.crossings p.1 p.2) =
          (Finset.univ : Finset (Fin m × Fin m)).filter
            fun p => p.1 < p.2 ∧ (c * y p.1 (event j)).re = (c * y p.2 (event j)).re := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hp, hθ⟩
          exact ⟨hp, ((hmem p.1 p.2 hp _).mp hθ).2⟩
        · rintro ⟨hp, he⟩
          exact ⟨hp, (hmem p.1 p.2 hp _).mpr ⟨hevI j, he⟩⟩
      rw [hfilter, Finset.sum_congr rfl fun p hp => hsign p.1 p.2
        (Finset.mem_filter.mp hp).2.1 _ ((hmem _ _ (Finset.mem_filter.mp hp).2.1 _).mpr
          ⟨hevI j, (Finset.mem_filter.mp hp).2.2⟩)]
      simp)
  rw [← h, SignedAdjacentWord.exponentSum_flatten, positiveWordSequence_length]
  push_cast
  exact Finset.sum_congr rfl fun j _ => PositiveAdjacentWord.exponentSum_toSigned (w j)

namespace MultiSheetData

variable {S : ℕ} (D : MultiSheetData S)

theorem multiSheetStrands_eq_mul (c : ℂ) (V : Fin S → ℂ → ℂ) (q : ℕ) (r : ℝ) (k : Fin S)
    (θ : ℝ) : multiSheetStrands c V q r k θ = c * multiSheetStrands 1 V q r k θ := by
  simp [multiSheetStrands]

theorem rootSheet_zero (k : Fin S) : D.rootSheet k 0 = 0 := by
  simp [rootSheet, zero_pow D.q_pos.ne']

/-- Exponent sum of the full-twist prefix. -/
theorem exponentSum_fullTwistWord_append (v : PositiveAdjacentWord S) :
    SignedAdjacentWord.exponentSum (PositiveAdjacentWord.toSigned (fullTwistWord S ++ v)) =
      ((S * (S - 1) : ℕ) : ℤ) + v.length := by
  rw [PositiveAdjacentWord.exponentSum_toSigned, List.length_append, fullTwistWord,
    torusWord_length]
  push_cast
  ring

/-- **The strict-transform event word** (sheet level of Theorem `J14:thm:factorization`
without the full-twist identification). -/
theorem exists_strict_event_word {c : ℂ} (hc : c ≠ 0)
    (hproj : ∀ k l, D.U k 0 ≠ D.U l 0 → (c * (D.U k 0 - D.U l 0)).re ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ D.R ∧
      (∀ r, 0 < r → r < r₀ → IsPeriodicStrandBraid (D.strict c r) D.τ ∧
        IsPeriodicStrandBraid (D.root 1 r) D.τ ∧
        ∀ θ k l, k ≠ l → (D.strict c r k θ).re = (D.strict c r l θ).re →
          0 < -deriv (fun t => (D.strict c r k t - D.strict c r l t).re) θ *
            (D.strict c r k θ - D.strict c r l θ).im) ∧
      (∀ r, 0 < r → r < r₀ → ∀ u v : ℝ,
        {θ | θ ∈ Icc u v ∧ ∃ k l, k ≠ l ∧ (D.strict c r k θ).re = (D.strict c r l θ).re}.Finite ∧
        {θ | θ ∈ Icc u v ∧ ∃ k l, k ≠ l ∧ (D.root c r k θ).re = (D.root c r l θ).re}.Finite) ∧
      ∀ r₁, 0 < r₁ → r₁ < r₀ →
        ∃ (b₁ : ℝ) (E : Finset ℝ) (N : ℕ) (event left right : Fin N → ℝ)
          (σ : Fin (N + 1) → Equiv.Perm (Fin S)) (w : Fin N → PositiveAdjacentWord S),
          (∀ t, t ∈ E ↔ t ∈ Icc b₁ (b₁ + 2 * π) ∧
            ∃ k l : Fin S, k ≠ l ∧ (D.strict c r₁ k t).re = (D.strict c r₁ l t).re) ∧
          b₁ ∉ E ∧ b₁ + 2 * π ∉ E ∧
          N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
          (∀ j : Fin N,
            b₁ < left j ∧ left j < event j ∧ event j < right j ∧ right j < b₁ + 2 * π ∧
            StrictMono (fun k => (D.strict c r₁ (σ j.castSucc k) (left j)).re) ∧
            StrictMono (fun k => (D.strict c r₁ (σ j.succ k) (right j)).re) ∧
            (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
            IsPositiveBraidEventWord (D.strict c r₁) (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
          (∀ j q, j < q → right j < left q) ∧
          (σ (Fin.last N)).trans D.τ = σ 0 ∧
          σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
            σ (Fin.last N) ∧
          (∀ r, 0 < r → r < r₀ → ∀ b : ℝ,
            IsRepresentedByPositiveWord (D.strict c r) b (b + 2 * π) (List.ofFn w).flatten) ∧
          (PositiveAdjacentWord.toSigned (List.ofFn w).flatten).cycleCount =
            permCycleCount D.τ ∧
          ∀ r, 0 < r → r < r₀ → ∀ b : ℝ,
            (∀ k l, k ≠ l → (D.root c r k b).re ≠ (D.root c r l b).re) →
            ∃ Dy : SheetCrossingData S (D.root 1 r) b c,
              (∀ k l, k < l → ∀ θ ∈ Dy.crossings k l, Dy.crossingSign k l θ = 1) ∧
              Dy.signedCount = SignedAdjacentWord.exponentSum
                (PositiveAdjacentWord.toSigned (fullTwistWord S ++ (List.ofFn w).flatten)) := by
  classical
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨rU, hrU, hrUR, hsepU, hU⟩ := exists_radius_multiSheet_positive_crossings D.q_pos
    D.R_pos D.analytic D.distinct hc hproj
  obtain ⟨rY, hrY, hrYR, hsepY, hY⟩ := exists_radius_multiSheet_positive_crossings D.q_pos
    D.R_pos D.rootSheet_analytic D.rootSheet_distinct hc
    (fun k l h => (h (by rw [D.rootSheet_zero, D.rootSheet_zero])).elim)
  set r₀ := min rU rY with hr₀
  have hr₀U : r₀ ≤ rU := min_le_left _ _
  have hr₀Y : r₀ ≤ rY := min_le_right _ _
  have hr₀pos : 0 < r₀ := lt_min hrU hrY
  -- Periodicity at every small radius.
  have hperU : ∀ r, 0 < r → r < r₀ → IsPeriodicStrandBraid (D.strict c r) D.τ := by
    intro r hr hrr
    have hrR : r < D.R := lt_of_lt_of_le (lt_of_lt_of_le hrr hr₀U) hrUR
    refine ⟨fun k => (multiSheetStrands_continuous D.analytic D.q hr.le hrR k), fun t => ?_,
      fun k t => D.strict_add_two_pi c hr.le hrR k t⟩
    exact (hU r hr (lt_of_lt_of_le hrr hr₀U)).2.1 t
  have hperY : ∀ r, 0 < r → r < r₀ → IsPeriodicStrandBraid (D.root 1 r) D.τ := by
    intro r hr hrr
    have hrR : r < D.R := lt_of_lt_of_le (lt_of_lt_of_le hrr hr₀Y) hrYR
    refine ⟨fun k => (multiSheetStrands_continuous D.rootSheet_analytic D.q hr.le hrR k),
      fun t => ?_, fun k t => D.root_add_two_pi 1 hr.le hrR k t⟩
    exact (D.isClosedStrandBraid_of_sheets D.rootSheet_analytic D.rootSheet_monodromy hrYR
      hsepY one_ne_zero hr (lt_of_lt_of_le hrr hr₀Y) t).injective t
      (left_mem_Icc.mpr (by linarith))
  refine ⟨r₀, hr₀pos, (min_le_left _ _).trans hrUR, fun r hr hrr => ⟨hperU r hr hrr,
    hperY r hr hrr, (hU r hr (lt_of_lt_of_le hrr hr₀U)).2.2.2.2.2.1⟩,
    fun r hr hrr u v => ⟨(hU r hr (lt_of_lt_of_le hrr hr₀U)).2.2.2.2.2.2 u v,
      (hY r hr (lt_of_lt_of_le hrr hr₀Y)).2.2.2.2.2.2 u v⟩, ?_⟩
  intro r₁ hr₁ hr₁r
  have hr₁U : r₁ < rU := lt_of_lt_of_le hr₁r hr₀U
  have hr₁Y : r₁ < rY := lt_of_lt_of_le hr₁r hr₀Y
  obtain ⟨hdiff₁, hinj₁, -, -, -, hcross₁, hfin₁⟩ := hU r₁ hr₁ hr₁U
  have hP₁ := hperU r₁ hr₁ hr₁r
  -- A regular base angle.
  obtain ⟨b₁, hb₁mem, hb₁⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset
    (hfin₁ 0 (2 * π)).toFinset
  have hb₁reg : ∀ k l, k ≠ l → (D.strict c r₁ k b₁).re ≠ (D.strict c r₁ l b₁).re := by
    intro k l hkl heq
    apply hb₁
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨hb₁mem.1.le, by linarith [hb₁mem.2, Real.two_le_pi]⟩, k, l, hkl, heq⟩
  have hd₁reg : ∀ k l, k ≠ l →
      (D.strict c r₁ k (b₁ + 2 * π)).re ≠ (D.strict c r₁ l (b₁ + 2 * π)).re := by
    intro k l hkl
    rw [hP₁.periodic k, hP₁.periodic l]
    exact hb₁reg _ _ (D.τ.injective.ne hkl)
  let E : Finset ℝ := (hfin₁ b₁ (b₁ + 2 * π)).toFinset
  have hE : ∀ t, t ∈ E ↔ t ∈ Icc b₁ (b₁ + 2 * π) ∧
      ∃ k l : Fin S, k ≠ l ∧ (D.strict c r₁ k t).re = (D.strict c r₁ l t).re := by
    intro t
    exact Set.Finite.mem_toFinset _
  have hbE : b₁ ∉ E := fun h => by
    obtain ⟨_, k, l, hkl, heq⟩ := (hE b₁).mp h
    exact hb₁reg k l hkl heq
  have hdE : b₁ + 2 * π ∉ E := fun h => by
    obtain ⟨_, k, l, hkl, heq⟩ := (hE _).mp h
    exact hd₁reg k l hkl heq
  obtain ⟨N, event, left, right, σ, w, hN, henum, hmono, -, -, hblocks, hsep, hσ, hperm, -,
      -, hrep⟩ := exists_positive_event_words_isRepresented (K := D.strict c r₁)
    (fun k => (hdiff₁ k).continuous) (by linarith) (fun t _ => hinj₁ t)
    (fun k => hP₁.periodic k b₁) E hE hbE hdE (fun θ _ k l hkl heq => hcross₁ θ k l hkl heq)
  set v := (List.ofFn w).flatten with hv
  -- Representation at every radius and base angle.
  have hrep_all : ∀ r, 0 < r → r < r₀ → ∀ b : ℝ,
      IsRepresentedByPositiveWord (D.strict c r) b (b + 2 * π) v := by
    intro r hr hrr b
    have hiso : ClosedStrandBraidIsotopic (D.strict c r) (D.strict c r₁) b₁ (b₁ + 2 * π) D.τ :=
      D.multiSheetStrands_radius_isotopic D.analytic D.monodromy hrUR hsepU hc hr
        (lt_of_lt_of_le hrr hr₀U) hr₁ hr₁U b₁
    exact (hperU r hr hrr).isRepresented_base (hrep.of_isotopic hiso) b
  -- The strict-transform crossing data at the reference radius.
  have hKeq : ∀ k θ, multiSheetStrands c D.U D.q r₁ k θ = c * D.strict 1 r₁ k θ :=
    fun k θ => multiSheetStrands_eq_mul c D.U D.q r₁ k θ
  have hdiffs : ∀ k, Differentiable ℝ (D.strict 1 r₁ k) :=
    multiSheetStrands_differentiable D.analytic D.q hr₁.le (lt_of_lt_of_le hr₁U hrUR)
  have hfuncU : (fun k θ => c * D.strict 1 r₁ k θ) = D.strict c r₁ :=
    funext fun k => funext fun θ => (hKeq k θ).symm
  obtain ⟨Du, hDusign, hDumem⟩ := exists_positive_sheetCrossingData (y := D.strict 1 r₁)
    (c := c) (b := b₁) hdiffs
    (by simpa only [hKeq] using hfin₁ b₁ (b₁ + 2 * π))
    (fun k l hkl => by simpa only [strict, hKeq] using hb₁reg k l hkl)
    (fun k l hkl => by simpa only [strict, hKeq] using hd₁reg k l hkl)
    (fun θ k l hkl heq => by
      simpa only [hKeq] using hcross₁ θ k l hkl (by simpa only [hKeq] using heq))
  have hevI : ∀ j, event j ∈ Icc b₁ (b₁ + 2 * π) := fun j =>
    ⟨((hblocks j).1.trans (hblocks j).2.1).le,
      ((hblocks j).2.2.1.trans (hblocks j).2.2.2.1).le⟩
  have hcover : ∀ θ ∈ Icc b₁ (b₁ + 2 * π),
      (∃ k l, k ≠ l ∧ (c * D.strict 1 r₁ k θ).re = (c * D.strict 1 r₁ l θ).re) →
      ∃ j, event j = θ := by
    rintro θ hθ ⟨k, l, hkl, heq⟩
    have hθE : θ ∈ E := (hE θ).mpr ⟨hθ, k, l, hkl, by simpa only [strict, hKeq] using heq⟩
    have hθs : θ ∈ E.sort (· ≤ ·) := (Finset.mem_sort _).mpr hθE
    rw [← henum, List.mem_ofFn] at hθs
    exact hθs
  have hDucount : Du.signedCount = v.length :=
    Du.signedCount_eq_length hDusign hDumem event hmono hevI hcover σ w
      (fun j => by rw [hfuncU]; exact (hblocks j).2.2.2.2.2.2.2)
  have hstrict₁ : IsClosedStrandBraid (D.strict 1 r₁) b₁ (b₁ + 2 * π) D.τ :=
    D.isClosedStrandBraid_of_sheets D.analytic D.monodromy hrUR hsepU one_ne_zero hr₁ hr₁U b₁
  have hwind₁ : windingNumber (strandDiscriminant (D.strict 1 r₁)) b₁ (b₁ + 2 * π) = v.length := by
    rw [← Du.signedCount_eq_windingNumber hc hstrict₁, hDucount]
  -- The winding number of the base circle.
  have hcirc : windingNumber (circlePath (r₁ ^ D.q)) b₁ (b₁ + 2 * π) = 1 := by
    have hρ : (((r₁ ^ D.q : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos hr₁ D.q).ne'
    have hloop : Complex.exp ((b₁ : ℂ) * Complex.I) =
        Complex.exp (((b₁ + 2 * π : ℝ) : ℂ) * Complex.I) := by
      rw [show (((b₁ + 2 * π : ℝ) : ℂ) * Complex.I) = (b₁ : ℂ) * Complex.I + 2 * π * Complex.I by
        push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have h := windingNumber_const_mul (γ := fun θ : ℝ => Complex.exp (θ * Complex.I))
      (u := b₁) (v := b₁ + 2 * π) (by linarith) (by fun_prop)
      (fun _ _ => Complex.exp_ne_zero _) hloop hρ
    change windingNumber (fun θ : ℝ => (((r₁ ^ D.q : ℝ)) : ℂ) * Complex.exp (θ * Complex.I))
      b₁ (b₁ + 2 * π) = 1
    rw [h, windingNumber_exp_mul_I]
  -- The root braid at the reference radius.
  have hrootwind : windingNumber (strandDiscriminant (D.root 1 r₁)) b₁ (b₁ + 2 * π) =
      ((S * (S - 1) : ℕ) : ℤ) + v.length := by
    have hroot : D.root 1 r₁ = fun k t => circlePath (r₁ ^ D.q) t * D.strict 1 r₁ k t :=
      funext fun k => funext fun t => D.root_eq 1 r₁ k t
    have hcont : ContinuousOn (circlePath (r₁ ^ D.q)) (Icc b₁ (b₁ + 2 * π)) :=
      (continuous_circlePath _).continuousOn
    have hne : ∀ t ∈ Icc b₁ (b₁ + 2 * π), circlePath (r₁ ^ D.q) t ≠ 0 := by
      intro t _
      apply norm_pos_iff.mp
      rw [norm_circlePath (pow_pos hr₁ D.q).le]
      exact pow_pos hr₁ D.q
    rw [hroot, windingNumber_strandDiscriminant_mul_left hstrict₁ hcont hne
      (circlePath_add_two_pi _ b₁).symm, hcirc, hwind₁]
    ring
  refine ⟨b₁, E, N, event, left, right, σ, w, hE, hbE, hdE, hN, henum, hmono, hblocks, hsep,
    hσ, hperm, hrep_all, hrep.cycleCount_eq (hP₁.isClosedStrandBraid b₁), ?_⟩
  -- Root crossing data at every radius and regular base angle.
  intro r hr hrr b hbreg
  have hrY' : r < rY := lt_of_lt_of_le hrr hr₀Y
  obtain ⟨-, -, -, -, -, hcrossY, hfinY⟩ := hY r hr hrY'
  have hPY := hperY r hr hrr
  have hKY : ∀ k θ, multiSheetStrands c D.rootSheet D.q r k θ = c * D.root 1 r k θ :=
    fun k θ => multiSheetStrands_eq_mul c D.rootSheet D.q r k θ
  have hdiffy : ∀ k, Differentiable ℝ (D.root 1 r k) :=
    multiSheetStrands_differentiable D.rootSheet_analytic D.q hr.le (lt_of_lt_of_le hrY' hrYR)
  have hPYc : ∀ k θ, D.root c r k (θ + 2 * π) = D.root c r (D.τ k) θ :=
    fun k θ => D.root_add_two_pi c hr.le (lt_of_lt_of_le hrY' hrYR) k θ
  obtain ⟨Dy, hDysign, -⟩ := exists_positive_sheetCrossingData (y := D.root 1 r)
    (c := c) (b := b) hdiffy
    (by simpa only [hKY] using hfinY b (b + 2 * π))
    (fun k l hkl => by simpa only [root, hKY] using hbreg k l hkl)
    (fun k l hkl => by
      have h := hbreg _ _ (D.τ.injective.ne hkl)
      rw [← hPYc, ← hPYc] at h
      simpa only [root, hKY] using h)
    (fun θ k l hkl heq => by
      simpa only [hKY] using hcrossY θ k l hkl (by simpa only [hKY] using heq))
  refine ⟨Dy, hDysign, ?_⟩
  have hisoY : ClosedStrandBraidIsotopic (D.root 1 r) (D.root 1 r₁) b (b + 2 * π) D.τ :=
    D.multiSheetStrands_radius_isotopic D.rootSheet_analytic D.rootSheet_monodromy hrYR hsepY
      one_ne_zero hr hrY' hr₁ hr₁Y b
  rw [Dy.signedCount_eq_windingNumber hc (hPY.isClosedStrandBraid b),
    hisoY.windingNumber_strandDiscriminant_eq,
    (hperY r₁ hr₁ hr₁r).windingNumber_base b₁ b, hrootwind,
    exponentSum_fullTwistWord_append]

end MultiSheetData

end OnLeConjecture.Analytic
