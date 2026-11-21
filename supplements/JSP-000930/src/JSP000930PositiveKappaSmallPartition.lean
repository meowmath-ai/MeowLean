import JSP000930PositiveEveryRealLocalReservePrefix

namespace JSP000930.Positive

open Cardinal JSP000933.PreparedModel JSP000933.RelativeOCA

variable {B : Type} [CompleteBooleanAlgebra B]

theorem aboveKappaValue_antitone (w : GroundContinuumSuccIndex → B) :
    Antitone (aboveKappaValue w) := by
  intro a b hab
  apply iSup_le
  intro i
  exact le_iSup (fun j : {j : GroundContinuumSuccIndex // a < j} => w j.val)
    ⟨i.val,hab.trans_lt i.property⟩

theorem unboundedKappaValue_mono {w v : GroundContinuumSuccIndex → B}
    (h : ∀ i,w i ≤ v i) : unboundedKappaValue w ≤ unboundedKappaValue v := by
  apply le_iInf
  intro b
  exact (iInf_le _ b).trans (iSup_le fun j => le_iSup_of_le j (h j.val))

theorem aboveKappaValue_iSup {I : Type} (w : I→GroundContinuumSuccIndex→B) (a : GroundContinuumSuccIndex) :
    aboveKappaValue (fun i => ⨆ n,w n i) a=⨆ n,aboveKappaValue (w n) a := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro n
    exact le_iSup_of_le n (le_iSup (fun j : {j : GroundContinuumSuccIndex // a < j} => w n j.val) i)
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup_of_le i (le_iSup (fun k => w k i.val) n)

theorem unboundedKappaValue_smallPartition (hB : BoundsSmallKappaNames B)
    {A : Type} (hA : Cardinal.mk A < GroundContinuumSucc)
    (w : A→GroundContinuumSuccIndex→B) :
    unboundedKappaValue (fun i => ⨆ n,w n i)=⨆ n,unboundedKappaValue (w n) := by
  apply le_antisymm
  · let f (i : GroundContinuumSuccIndex) := ⨆ n,w n i
    let a := unboundedKappaValue f
    let b := ⨆ n,unboundedKappaValue (w n)
    change a≤b
    by_contra h
    let m := a⊓bᶜ
    have hM : m≠⊥ := fun he =>
      h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    let V (n : A) (j : GroundContinuumSuccIndex) := (aboveKappaValue (w n) j)ᶜ
    have hV (n : A) : m≤⨆ j,V n j := by
      have h' : m≤(unboundedKappaValue (w n))ᶜ :=
        inf_le_right.trans (compl_le_compl (le_iSup (fun k => unboundedKappaValue (w k)) n))
      unfold unboundedKappaValue at h'
      simpa only [compl_iInf,V] using h'
    have hU : m≤⨆ j : GroundContinuumSuccIndex,⨅ n,⨆ i : {i : GroundContinuumSuccIndex // i<j},V n i.val :=
      (le_iInf hV).trans (hB A hA V)
    have h0 : m≤⊥ := by
      apply (le_inf le_rfl hU).trans
      rw [inf_iSup_eq]
      apply iSup_le
      intro j
      have h1 : m≤aboveKappaValue f j := inf_le_left.trans (iInf_le _ j)
      have h2 : (⨅ n,⨆ i : {i : GroundContinuumSuccIndex // i<j},V n i.val)≤(aboveKappaValue f j)ᶜ := by
        unfold f
        rw [aboveKappaValue_iSup,compl_iSup]
        apply le_iInf
        intro n
        apply (iInf_le _ n).trans
        apply iSup_le
        intro i
        exact compl_le_compl (aboveKappaValue_antitone (w n) i.property.le)
      exact (inf_le_inf h1 h2).trans (disjoint_iff_inf_le.mp (disjoint_compl_right :
        Disjoint (aboveKappaValue f j) (aboveKappaValue f j)ᶜ))
    exact hM (le_bot_iff.mp h0)
  · exact iSup_le (fun n => unboundedKappaValue_mono (fun i => le_iSup (fun k => w k i) n))

end JSP000930.Positive
