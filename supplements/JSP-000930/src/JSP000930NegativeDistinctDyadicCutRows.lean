import JSP000930PositiveActualDyadicCutName
import JSP000930NegativeDistinctSiteCapturesTrial

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Positive.Cohen

open JSP000933.MarkedForcing JSP000933.BooleanCompletion
  JSP000930.Positive.Dyadic JSP000930.BooleanAnalysis

private theorem lowerTwo_right_lt_mid (s : Interval) :
    (s.follow [false,false]).right < s.mid := by
  simp only [Interval.follow,Interval.split,Interval.mid]
  linarith [s.positive]

private theorem mid_lt_upperTwo_left (s : Interval) :
    s.mid < (s.follow [true,true]).left := by
  simp only [Interval.follow,Interval.split,Interval.mid]
  linarith [s.positive]

private theorem two_rows_extend_words {I : Type} (p : Trace (I × ℕ))
    {i j : I} (hij : i ≠ j) (u v : List Bool) :
    ∃ r : Trace (I × ℕ), r ≤ p ∧
      WordMatches r i (completeRowWord p i ++ u) ∧
      WordMatches r j (completeRowWord p j ++ v) := by
  obtain ⟨q,hqp,hqi,hNew⟩ := exists_append_no_new_other_row p i u
  let w := completeRowWord p j ++ v
  obtain ⟨r,hrq,hrj⟩ := extends_word_of_agrees q j w (by
    intro n hn
    have hn' := hNew _ hn (Ne.symm hij)
    exact (hqp.2 _ hn').trans (completeRowWord_agrees_append p j v n hn'))
  refine ⟨r,hrq.trans hqp,fun n => ?_,hrj⟩
  obtain ⟨hn,hbit⟩ := hqi n
  exact ⟨hrq.1 hn,(hrq.2 _ hn).trans hbit⟩

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem weighted_dyadic_eq_avoided
    (i j : I) (s t : List Bool) (h : (unitInterval.follow s).right <
      (unitInterval.follow t).left) (a : CohenBA B (I × ℕ))
    (ha : a ≤ wordValue B i s) (hb : a ≤ wordValue B j t)
    :
    Disjoint a (dyadicCutName (B := B) i =ᴮ dyadicCutName (B := B) j) := by
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (unitInterval.follow s).right
  have h0 := ha.trans (dyadicCutBit_above_right i s q hq.ge)
  have h1 := hb.trans (dyadicCutBit_below_left j t q (hq.trans_lt h))
  apply disjoint_iff_inf_le.mpr
  let c := a ⊓ (dyadicCutName (B := B) i =ᴮ dyadicCutName (B := B) j)
  have hmemJ : c ≤ ratName q ∈ᴮ dyadicCutName (B := B) j := by
    rw [dyadicCutName_mem]
    exact inf_le_left.trans h1
  have hmemI : c ≤ ratName q ∈ᴮ dyadicCutName (B := B) i :=
    bSet.subst_congr_mem_right' (bv_symm inf_le_right) hmemJ
  rw [dyadicCutName_mem] at hmemI
  exact (le_inf hmemI (inf_le_left.trans h0)).trans_eq inf_compl_eq_bot

theorem dyadicCutName_rows_apart
    {i j : I} (hij : i ≠ j) :
    (dyadicCutName (B := B) i =ᴮ dyadicCutName (B := B) j) = ⊥ := by
  apply value_eq_bot_of_dense_avoidance
  intro p hp
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 p hp
  let u := completeRowWord t.trace i
  let v := completeRowWord t.trace j
  by_cases h : (unitInterval.follow u).mid ≤ (unitInterval.follow v).mid
  · obtain ⟨q,hqt,hi,hj⟩ := two_rows_extend_words t.trace hij [false,false] [true,true]
    let r : TotalCondition (valuedCohen B (I × ℕ)) := ⟨t.mask,q,t.nonzero,le_top⟩
    have hr : r ≤ t := (cohen_total_le_iff _ _).mpr ⟨le_rfl,hqt⟩
    have hs : (unitInterval.follow (u ++ [false,false])).right <
        (unitInterval.follow (v ++ [true,true])).left := by
      rw [Interval.follow_append,Interval.follow_append]
      exact (lowerTwo_right_lt_mid _).trans_le (h.trans (mid_lt_upperTwo_left _).le)
    exact ⟨imageCondition r,imageCondition_ne_bot_r50 r,
      (imageCondition_mono_r50 hr).trans ht,
      (weighted_dyadic_eq_avoided i j _ _ hs _ (image_le_wordValue r i _ hi)
        (image_le_wordValue r j _ hj)).eq_bot⟩
  · obtain ⟨q,hqt,hi,hj⟩ := two_rows_extend_words t.trace hij [true,true] [false,false]
    let r : TotalCondition (valuedCohen B (I × ℕ)) := ⟨t.mask,q,t.nonzero,le_top⟩
    have hr : r ≤ t := (cohen_total_le_iff _ _).mpr ⟨le_rfl,hqt⟩
    have hs : (unitInterval.follow (v ++ [false,false])).right <
        (unitInterval.follow (u ++ [true,true])).left := by
      rw [Interval.follow_append,Interval.follow_append]
      exact (lowerTwo_right_lt_mid _).trans_le ((le_of_not_ge h).trans (mid_lt_upperTwo_left _).le)
    have hd := weighted_dyadic_eq_avoided j i _ _ hs _ (image_le_wordValue r j _ hj)
      (image_le_wordValue r i _ hi)
    exact ⟨imageCondition r,imageCondition_ne_bot_r50 r,
      (imageCondition_mono_r50 hr).trans ht,
      (hd.mono_right (bv_symm le_rfl)).eq_bot⟩

end JSP000930.Positive.Cohen
