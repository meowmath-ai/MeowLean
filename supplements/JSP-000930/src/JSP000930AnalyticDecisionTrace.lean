import JSP000930AnalyticTaylorPrefix

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure CutDecisionTrace (p : ℕ → B) (u : RatPresentation → B) (x : ℝ) : Prop where
  below : ∀ q : RatPresentation, (q.value : ℝ) < x → ∃ N, p N ≤ u q
  above : ∀ q : RatPresentation, x < (q.value : ℝ) → ∃ N, p N ≤ (u q)ᶜ

theorem eventuallyMeet {p : ℕ → B} (h : Antitone p) {a b : B}
    (ha : ∃ n, p n ≤ a) (hb : ∃ n, p n ≤ b) : ∃ n, p n ≤ a ⊓ b := by
  obtain ⟨n,hn⟩ := ha
  obtain ⟨m,hm⟩ := hb
  exact ⟨max n m,le_inf ((h (le_max_left _ _)).trans hn) ((h (le_max_right _ _)).trans hm)⟩

theorem trace_subset_le {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (hsub : m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v) : x ≤ y := by
  by_contra hxy
  obtain ⟨t,hyt,htx⟩ := exists_rat_btwn (lt_of_not_ge hxy)
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective t
  obtain ⟨n,hn⟩ := eventuallyMeet h
    (hu.below q (by rwa [hq])) (hv.above q (by rwa [hq]))
  rw [weightedRationalSet_subset] at hsub
  have h' := (hpm n).trans (hsub.trans (iInf_le _ q))
  rw [← deduction] at h'
  have hvq := (le_inf le_rfl (hn.trans inf_le_left)).trans h'
  exact hnz n (le_bot_iff.mp ((le_inf hvq (hn.trans inf_le_right)).trans (by simp)))

theorem trace_cut_eq {p : ℕ → B} (h : Antitone p) (hnz : ∀ n, p n ≠ ⊥)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (he : m ≤ weightedRationalSet u =ᴮ weightedRationalSet v) : x = y := by
  rw [bSet.eq_iff_subset_subset] at he
  exact le_antisymm (trace_subset_le h hnz hpm hu hv (he.trans inf_le_left))
    (trace_subset_le h hnz hpm hv hu (he.trans inf_le_right))

theorem CutDecisionTrace.add {p : ℕ → B} (h : Antitone p)
    {m : B} (hpm : ∀ n, p n ≤ m) {u v : RatPresentation → B} {x y : ℝ}
    (hu : CutDecisionTrace p u x) (hv : CutDecisionTrace p v y)
    (hU : ProperCutOn m u) (hV : ProperCutOn m v) :
    CutDecisionTrace p (addCutBits u v) (x+y) := by
  constructor
  · intro q hq
    let e := (x+y-(q.value : ℝ))/3
    have he : 0 < e := by dsimp [e]; linarith
    obtain ⟨aa,hal,hau⟩ := exists_rat_btwn (show x-e < x by linarith)
    obtain ⟨bb,hbl,hbu⟩ := exists_rat_btwn (show y-e < y by linarith)
    obtain ⟨a,ha⟩ := ratPresentation_value_surjective aa
    obtain ⟨b,hb⟩ := ratPresentation_value_surjective bb
    have hab : q.value < a.value+b.value := by
      have ht : (q.value : ℝ) < (a.value : ℝ)+(b.value : ℝ) := by
        rw [ha,hb]
        dsimp [e] at hal hbl
        linarith
      exact_mod_cast ht
    obtain ⟨n,hn⟩ := eventuallyMeet h (hu.below a (by rwa [ha])) (hv.below b (by rwa [hb]))
    exact ⟨n,hn.trans (le_iSup_of_le a (le_iSup_of_le b (le_iSup (fun _ : q.value < a.value+b.value => u a ⊓ v b) hab)))⟩
  · intro q hq
    let e := ((q.value : ℝ)-(x+y))/3
    have he : 0 < e := by dsimp [e]; linarith
    obtain ⟨aa,hal,hau⟩ := exists_rat_btwn (show x < x+e by linarith)
    obtain ⟨bb,hbl,hbu⟩ := exists_rat_btwn (show y < y+e by linarith)
    obtain ⟨a,ha⟩ := ratPresentation_value_surjective aa
    obtain ⟨b,hb⟩ := ratPresentation_value_surjective bb
    obtain ⟨t,ht⟩ := ratPresentation_value_surjective (a.value+b.value)
    have htq : t.value ≤ q.value := by
      have hh : (t.value : ℝ) ≤ (q.value : ℝ) := by
        rw [ht,Rat.cast_add,ha,hb]
        dsimp [e] at hau hbu
        linarith
      exact_mod_cast hh
    obtain ⟨n,hn⟩ := eventuallyMeet h (hu.above a (by rwa [ha])) (hv.above b (by rwa [hb]))
    have hUn := properCutOn_mono (hpm n) hU
    have hVn := properCutOn_mono (hpm n) hV
    have hg := addCutBits_bounded_below u v (p n) a b t ht
      (hn.trans inf_le_left) (hn.trans inf_le_right)
      (fun k hka => hUn.2.2.1 a k hka) (fun k hkb => hVn.2.2.1 b k hkb)
    exact ⟨n,hg.trans (compl_le_compl (addCutBits_downward u v htq))⟩

theorem CutDecisionTrace.neg {p : ℕ → B} {m : B} (hpm : ∀ n, p n ≤ m)
    {u : RatPresentation → B} {x : ℝ} (hu : CutDecisionTrace p u x)
    (hU : ProperCutOn m u) : CutDecisionTrace p (negCutBits u) (-x) := by
  constructor
  · intro q hq
    obtain ⟨rr,hrl,hru⟩ := exists_rat_btwn (show x < -(q.value : ℝ) by linarith)
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective rr
    obtain ⟨n,hn⟩ := hu.above r (by rwa [hr])
    have hqr : q.value < -r.value := by
      have hh : (q.value : ℝ) < -(r.value : ℝ) := by rw [hr]; linarith
      exact_mod_cast hh
    exact ⟨n,hn.trans (le_iSup_of_le r (le_iSup (fun _ : q.value < -r.value => (u r)ᶜ) hqr))⟩
  · intro q hq
    obtain ⟨rr,hrl,hru⟩ := exists_rat_btwn (show -(q.value : ℝ) < x by linarith)
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective rr
    obtain ⟨n,hn⟩ := hu.below r (by rwa [hr])
    refine ⟨n,le_compl_iff_disjoint_right.mpr ?_⟩
    rw [disjoint_iff_inf_le,negCutBits,inf_iSup_eq]
    refine iSup_le fun t => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun ht => ?_
    have htr : t.value ≤ r.value := by
      have htx : (q.value : ℝ) < -(t.value : ℝ) := by exact_mod_cast ht
      have hrr : (t.value : ℝ) ≤ (r.value : ℝ) := by rw [hr]; linarith
      exact_mod_cast hrr
    have ht' := (le_inf (hpm n) hn).trans (hU.2.2.1 t r htr)
    exact (inf_le_inf_right _ ht').trans (by simp)

theorem CutDecisionTrace.interval {p : ℕ → B} (h : Antitone p)
    {u : RatPresentation → B} {x : ℝ} (hu : CutDecisionTrace p u x)
    (a b : RatPresentation) (ha : (a.value : ℝ) < x) (hb : x < (b.value : ℝ)) :
    ∃ n, p n ≤ intervalBits u a b := by
  obtain ⟨rr,hrx,hrb⟩ := exists_rat_btwn hb
  obtain ⟨r,hr⟩ := ratPresentation_value_surjective rr
  have hrb' : r.value < b.value := by
    have h' : (r.value : ℝ) < (b.value : ℝ) := by rwa [hr]
    exact_mod_cast h'
  obtain ⟨n,hn⟩ := eventuallyMeet h (hu.below a ha) (hu.above r (by rwa [hr]))
  exact ⟨n,le_inf (hn.trans inf_le_left)
    ((hn.trans inf_le_right).trans (le_iSup_of_le r (le_iSup (fun _ : r.value < b.value => (u r)ᶜ) hrb')))⟩

end JSP000930.BooleanAnalysis
