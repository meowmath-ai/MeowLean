import JSP000930PositiveCompatibleWords
import JSP000930AnalyticRoundedLimit
import JSP000933BooleanNamedCliqueStage
import JSP000933MarkedNameTransport

open scoped Flypitch bSet

namespace JSP000930.Positive.Cohen

open JSP000930.Positive.Dyadic JSP000930.BooleanAnalysis

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def dyadicCutBits (i : I) (q : RatPresentation) : CohenBA B (I × ℕ) :=
  ⨆ w : {w : List Bool // q.value < (unitInterval.follow w).left},
    wordValue B i w.val

noncomputable def dyadicCutName
    (i : I) :
    bSet (CohenBA B (I × ℕ)) :=
  weightedRationalSet (dyadicCutBits (B := B) i)

theorem dyadicCutName_mem
    (i : I) (q : RatPresentation) :
    (ratName q ∈ᴮ dyadicCutName (B := B) i) = dyadicCutBits (B := B) i q :=
  ratName_mem_weightedRationalSet _ _

theorem dyadicCutBit_below_left (i : I) (w : List Bool) (q : RatPresentation)
    (h : q.value < (unitInterval.follow w).left) :
    wordValue B i w ≤ dyadicCutBits (B := B) i q :=
  le_iSup (fun t : {t : List Bool // q.value < (unitInterval.follow t).left} => wordValue B i t.val) ⟨w,h⟩

theorem dyadicCutBit_above_right (i : I) (w : List Bool) (q : RatPresentation)
    (h : (unitInterval.follow w).right ≤ q.value) :
    wordValue B i w ≤ (dyadicCutBits (B := B) i q)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iSup_iff.mpr
  intro v
  rcases words_comparable_or_disagree w v.val with ⟨s,hs⟩ | ⟨s,hs⟩ | ⟨n,hw,hv,hne⟩
  · have h' : (unitInterval.follow v.val).right ≤ (unitInterval.follow w).right := by
      rw [hs,Interval.follow_append]
      exact ((unitInterval.follow w).follow_inside s).2
    exact False.elim (v.property.not_ge
      ((unitInterval.follow v.val).positive.le.trans (h'.trans h)))
  · have h' : (unitInterval.follow v.val).left ≤ (unitInterval.follow w).left := by
      rw [hs,Interval.follow_append]
      exact ((unitInterval.follow v.val).follow_inside s).1
    exact False.elim (v.property.not_ge
      (h'.trans ((unitInterval.follow w).positive.le.trans h)))
  · exact wordValue_disjoint_of_disagree i w v.val n hw hv hne

theorem dyadicCutBits_downward (i : I) {q r : RatPresentation}
    (h : q.value ≤ r.value) :
    dyadicCutBits (B := B) i r ≤ dyadicCutBits (B := B) i q := by
  apply iSup_le
  intro w
  exact dyadicCutBit_below_left i w.val q (h.trans_lt w.property)

theorem dyadicCutBits_ext (i : I) {q r : RatPresentation} (h : q.value = r.value) :
    dyadicCutBits (B := B) i q = dyadicCutBits (B := B) i r :=
  le_antisymm (dyadicCutBits_downward i h.ge) (dyadicCutBits_downward i h.le)

theorem dyadicCutBits_rounded (i : I) (q : RatPresentation) :
    dyadicCutBits (B := B) i q =
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value),dyadicCutBits (B := B) i r := by
  apply le_antisymm
  · apply iSup_le
    intro w
    let a := (unitInterval.follow w.val).left
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective ((q.value+a)/2)
    have hw : q.value < a := w.property
    have hq : q.value < r.value := by rw [hr]; linarith
    have hA : r.value < a := by rw [hr]; linarith
    exact (dyadicCutBit_below_left i w.val r hA).trans (le_iSup_of_le r (le_iSup (fun _ : q.value < r.value => dyadicCutBits (B := B) i r) hq))
  · exact iSup_le fun r => iSup_le fun h => dyadicCutBits_downward i h.le

theorem wordValue_nil (i : I) : wordValue B i [] = ⊤ := by
  simp [wordValue]

theorem dyadicCutBits_all_negative (i : I) (q : RatPresentation) (h : q.value < 0) :
    dyadicCutBits (B := B) i q = ⊤ := by
  apply top_unique
  rw [← wordValue_nil i]
  exact dyadicCutBit_below_left i [] q h

theorem dyadicCutBits_no_above_one (i : I) (q : RatPresentation) (h : 1 ≤ q.value) :
    dyadicCutBits (B := B) i q = ⊥ := by
  apply compl_eq_top.mp
  apply top_unique
  rw [← wordValue_nil i]
  exact dyadicCutBit_above_right i [] q h

end JSP000930.Positive.Cohen
