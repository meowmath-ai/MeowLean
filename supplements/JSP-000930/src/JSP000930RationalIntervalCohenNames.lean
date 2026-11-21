import JSP000930PositiveActualDyadicCutName
import JSP000930AnalyticRealAxisName

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Dyadic JSP000930.Positive.Cohen JSP000930.BooleanAnalysis
  JSP000933.SetLanguage

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def intervalCutBits (i : I) (s : Interval) (q : RatPresentation) :
    CohenBA B (I × ℕ) :=
  ⨆ w : {w : List Bool // q.value < (s.follow w).left}, wordValue B i w.1

theorem intervalCut_below_left (i : I) (s : Interval) (w : List Bool)
    (q : RatPresentation) (h : q.value < (s.follow w).left) :
    wordValue B i w ≤ intervalCutBits (B := B) i s q :=
  le_iSup (fun t : {t : List Bool // q.value < (s.follow t).left} => wordValue B i t.val) ⟨w,h⟩

theorem intervalCut_above_right (i : I) (s : Interval) (w : List Bool)
    (q : RatPresentation) (h : (s.follow w).right ≤ q.value) :
    wordValue B i w ≤ (intervalCutBits (B := B) i s q)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iSup_iff.mpr
  intro v
  rcases words_comparable_or_disagree w v.val with ⟨r,hr⟩ | ⟨r,hr⟩ | ⟨n,hw,hv,hne⟩
  · have h' : (s.follow v.val).right ≤ (s.follow w).right := by
      rw [hr,Interval.follow_append]
      exact ((s.follow w).follow_inside r).2
    exact False.elim (v.property.not_ge
      ((s.follow v.val).positive.le.trans (h'.trans h)))
  · have h' : (s.follow v.val).left ≤ (s.follow w).left := by
      rw [hr,Interval.follow_append]
      exact ((s.follow v.val).follow_inside r).1
    exact False.elim (v.property.not_ge
      (h'.trans ((s.follow w).positive.le.trans h)))
  · exact wordValue_disjoint_of_disagree i w v.val n hw hv hne

theorem intervalCut_downward (i : I) (s : Interval) {q r : RatPresentation}
    (h : q.value ≤ r.value) :
    intervalCutBits (B := B) i s r ≤ intervalCutBits (B := B) i s q := by
  apply iSup_le
  intro w
  exact intervalCut_below_left i s w.val q (h.trans_lt w.property)

theorem intervalCut_rounded (i : I) (s : Interval) (q : RatPresentation) :
    intervalCutBits (B := B) i s q ≤
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), intervalCutBits (B := B) i s r := by
  apply iSup_le
  intro w
  let a := (s.follow w.val).left
  obtain ⟨r,hr⟩ := ratPresentation_value_surjective ((q.value + a) / 2)
  have hw : q.value < a := w.property
  have hq : q.value < r.value := by rw [hr]; linarith
  have hA : r.value < a := by rw [hr]; linarith
  exact (intervalCut_below_left i s w.val r hA).trans (le_iSup_of_le r (le_iSup (fun _ : q.value < r.value => intervalCutBits (B := B) i s r) hq))

theorem intervalCut_proper (i : I) (s : Interval) :
    ProperCutOn (⊤ : CohenBA B (I × ℕ)) (intervalCutBits (B := B) i s) := by
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨q,hq⟩ := ratPresentation_value_surjective (s.left - 1)
    have hql : q.value < (s.follow []).left := by
      rw [hq]
      change s.left - 1 < s.left
      linarith
    rw [← wordValue_nil i]
    exact (intervalCut_below_left i s [] q hql).trans (le_iSup (intervalCutBits (B := B) i s) q)
  · obtain ⟨q,hq⟩ := ratPresentation_value_surjective s.right
    have hqr : (s.follow []).right ≤ q.value := by
      simpa only [hq, Interval.follow] using (show s.right ≤ s.right from le_rfl)
    rw [← wordValue_nil i]
    exact (intervalCut_above_right i s [] q hqr).trans (le_iSup (fun r => (intervalCutBits (B := B) i s r)ᶜ) q)
  · intro q r h
    exact inf_le_right.trans (intervalCut_downward i s h)
  · intro q
    exact inf_le_right.trans (intervalCut_rounded i s q)

noncomputable def intervalComplexName (i j : I) (s t : Interval) :
    bSet (CohenBA B (I × ℕ)) :=
  bSet.pair (weightedRationalSet (intervalCutBits (B := B) i s))
    (weightedRationalSet (intervalCutBits (B := B) j t))

theorem intervalComplex_forces_complex {n : ℕ}
    (v : DVec (V (CohenBA B (I × ℕ))) n) (i j : I) (s t : Interval) :
    let w : DVec (V (CohenBA B (I × ℕ))) (n+1) :=
      DVec.cons (intervalComplexName (B := B) i j s t) v
    let Z : JSP000933.SetLanguage.STerm (n+1) :=
      bd_var ⟨0,Nat.succ_pos n⟩
    (⊤ : CohenBA B (I × ℕ)) ≤ bTruth w (JSP000930.AnalyticSyntax.complex_f Z) := by
  change (⊤ : CohenBA B (I × ℕ)) ≤ bTruth
    (DVec.cons (intervalComplexName (B := B) i j s t) v)
    (JSP000930.AnalyticSyntax.complex_f (bd_var ⟨0,Nat.succ_pos n⟩))
  apply JSP000930.AnalyticSyntax.forces_complex_pair_of_cutData
    _ _ (intervalCutBits (B := B) i s) (intervalCutBits (B := B) j t) ⊤
  · exact bSet.bv_refl
  · exact intervalCut_proper i s
  · exact intervalCut_proper j t

end JSP000930.Negative.Cohen
