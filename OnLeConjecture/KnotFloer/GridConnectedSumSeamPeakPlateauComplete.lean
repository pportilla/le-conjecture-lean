/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauEndpoints

/-! # Exclusion of complete seam paths with northeast counts `1,2,2,1`

All retained endpoint pairs are allowed. The two middle configurations are
excluded by their actual entry and exit rectangles, respectively.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- No complete three-transition path has middle northeast counts two and two.
No equality of retained factor states is required. -/
theorem seamPeakPlateau_impossible (p q : SeamRetainedIndex n m)
    (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 2)
    (hnext : (seamNortheastColumns c.val.val).card = 2) (hne : b ≠ c) : False := by
  have hentry := seamMatchingEntry_northeast_card p a e
  have hexit := seamMatchingExit_northeast_card q d f
  have hb : (seamNortheastColumns b.val.val).card =
      (seamNortheastColumns a.val.val).card + 1 := by omega
  have hd : (seamNortheastColumns c.val.val).card =
      (seamNortheastColumns d.val.val).card + 1 := by omega
  have hcard : (seamSouthwestColumns b.val.val).card = 3 := by
    rw [seamSouthwestColumns_card, hmid]
  have hcard' : (seamSouthwestColumns c.val.val).card = 3 := by
    rw [seamSouthwestColumns_card, hnext]
  obtain ⟨D, hDn, hDv, hcase⟩ :=
    seamPeakPlateau_middle_cases a b c d r t u hr ht hu hne hb hd hcard hcard'
  rcases hcase with ⟨hrL, htL, htR, hRD, _, _, _, _⟩ |
      ⟨_, htL, htR, _, huL, _, _, _⟩
  · exact seamPeakPlateau_high_first_no_entry p a b c e r t he hr ht hb
      hcard hcard' hrL D hDn hDv htL htR hRD
  · exact seamPeakPlateau_high_third_no_exit q b c d t u f ht hu hf hd hcard hcard'
      (seamMatchingBirth_first_lt_third a b r hr hb (by omega)) huL D hDn hDv htL htR

/-- The native three-transition correction type has no plateau sector `1,2,2,1`. -/
theorem seamCorrectionThree_not_peak_plateau (p q : SeamRetainedIndex n m)
    (path : SeamCorrectionPath 3 p q) :
    ¬ ((seamNortheastColumns path.2.2.2.1.1.val.val).card = 2 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 2) := by
  rcases path with ⟨a, d, e, ⟨b, r, ⟨c, t, ⟨d', u, tail⟩⟩⟩, f⟩
  have hlast : d' = d := tail.property
  subst d'
  rintro ⟨hmid, hnext⟩
  exact seamPeakPlateau_impossible p q a b c d e.val r.val t.val u.val f.val
    e.property r.property.2 t.property.2 u.property.2 f.property hmid hnext t.property.1

end OnLeConjecture.KnotFloer.GridFull
