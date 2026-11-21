import JSP000930PolynomialRadiusBudgetDensity

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanCompletion

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def positiveCutValue (u : RatPresentation → B) : B :=
  ⨆ r : {r : RatPresentation // 0 < r.value}, u r.1

noncomputable def reciprocalCutBits (u : RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ r : RatPresentation, ⨆ (_ : 0 < r.value ∧ q.value * r.value < 1), (u r)ᶜ

theorem map_positiveCutValue (F : CompleteValueMap B C) (u : RatPresentation → B) :
    F.toFun (positiveCutValue u) = positiveCutValue (mapCut F u) := by
  simp only [positiveCutValue, F.map_iSup, mapCut]

theorem map_reciprocalCutBits (F : CompleteValueMap B C) (u : RatPresentation → B) :
    mapCut F (reciprocalCutBits u) = reciprocalCutBits (mapCut F u) := by
  funext q
  simp only [mapCut, reciprocalCutBits, F.map_iSup, map_iSup_prop930 F, F.map_compl]

theorem reciprocalCut_downward (u : RatPresentation → B) {q t : RatPresentation}
    (hqt : q.value ≤ t.value) : reciprocalCutBits u t ≤ reciprocalCutBits u q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  exact le_iSup_of_le r (le_iSup (fun _ : 0 < r.value ∧ q.value * r.value < 1 => (u r)ᶜ)
    ⟨hr.1,(mul_le_mul_of_nonneg_right hqt hr.1.le).trans_lt hr.2⟩)

theorem reciprocalCut_rounded (u : RatPresentation → B) (q : RatPresentation) :
    reciprocalCutBits u q ≤
      ⨆ t : RatPresentation, ⨆ (_ : q.value < t.value), reciprocalCutBits u t := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  have hqr : q.value < 1 / r.value := (lt_div_iff₀ hr.1).mpr hr.2
  obtain ⟨t,ht⟩ := ratPresentation_value_surjective ((q.value + 1 / r.value) / 2)
  have hqt : q.value < t.value := by rw [ht]; linarith
  have htr : t.value < 1 / r.value := by rw [ht]; linarith
  exact le_iSup_of_le t (le_iSup_of_le hqt
    (le_iSup_of_le r (le_iSup (fun _ : 0 < r.value ∧ t.value * r.value < 1 => (u r)ᶜ)
      ⟨hr.1,(lt_div_iff₀ hr.1).mp htr⟩)))

private theorem absentUp {p : B} {u : RatPresentation → B}
    (h : ProperCutOn p u) {q r : RatPresentation} (hqr : q.value ≤ r.value) :
    p ⊓ (u q)ᶜ ≤ (u r)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  have hx : (p ⊓ (u q)ᶜ) ⊓ u r ≤ u q :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans (h.2.2.1 q r hqr)
  have hy : (p ⊓ (u q)ᶜ) ⊓ u r ≤ (u q)ᶜ := inf_le_left.trans inf_le_right
  exact (le_inf hx hy).trans_eq inf_compl_eq_bot'

theorem reciprocalCut_nonempty {p : B} {u : RatPresentation → B}
    (h : ProperCutOn p u) :
    p ≤ ⨆ q : RatPresentation, reciprocalCutBits u q := by
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (-1)
  apply le_iSup_of_le q
  apply (le_inf le_rfl h.2.1).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  obtain ⟨r,hr⟩ := ratPresentation_value_surjective (max a.value 1)
  have ha : a.value ≤ r.value := by rw [hr]; exact le_max_left _ _
  have hr₀ : 0 < r.value := by
    rw [hr]
    exact zero_lt_one.trans_le (le_max_right _ _)
  have hqr : q.value * r.value < 1 := by rw [hq, neg_one_mul]; linarith
  exact (absentUp h ha).trans (le_iSup_of_le r (le_iSup (fun _ : 0 < r.value ∧ q.value * r.value < 1 => (u r)ᶜ) ⟨hr₀,hqr⟩))

theorem reciprocalCut_bounded {p : B} {u : RatPresentation → B}
    (h : ProperCutOn p u) (hpos : p ≤ positiveCutValue u) :
    p ≤ ⨆ q : RatPresentation, (reciprocalCutBits u q)ᶜ := by
  apply (le_inf le_rfl hpos).trans
  unfold positiveCutValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (1 / a.1.value)
  apply le_iSup_of_le q
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iSup_iff.mpr
  intro r
  apply disjoint_iSup_iff.mpr
  intro hp
  have hRa : r.value ≤ a.1.value := by
    have H := hp.2
    rw [hq, div_mul_eq_mul_div, one_mul] at H
    have H' := (div_lt_iff₀ a.2).mp H
    simpa only [one_mul] using H'.le
  have hd : p ⊓ u a.1 ≤ u r := h.2.2.1 r a.1 hRa
  exact disjoint_compl_right.mono_left hd

theorem reciprocalCut_proper {p : B} {u : RatPresentation → B}
    (h : ProperCutOn p u) (hpos : p ≤ positiveCutValue u) :
    ProperCutOn p (reciprocalCutBits u) :=
  ⟨reciprocalCut_nonempty h, reciprocalCut_bounded h hpos,
    (fun _ _ hqr => inf_le_right.trans (reciprocalCut_downward u hqr)),
    (fun q => inf_le_right.trans (reciprocalCut_rounded u q))⟩

end JSP000930.BooleanAnalysis
