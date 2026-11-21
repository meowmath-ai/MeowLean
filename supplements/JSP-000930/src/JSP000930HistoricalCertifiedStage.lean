import JSP000930HistoricalStepAdmission

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing

variable {A B N : Type} [LinearOrder A] [WellFoundedLT A]
  [CompleteBooleanAlgebra B] {a b : A}

noncomputable def historicalCertifiedCondition (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) (p : GoodPrefix old) :
    TotalCondition (certifiedQ Q) := by
  let r := historyCutPrefix hab.le old hP p
  refine ⟨imageCondition r,((p.trace a).getD (⊤,⊤)).2,imageCondition_ne_bot_r50 r,?_⟩
  change imageCondition r ≤ CertifiedStageLabel.admits Q ((p.trace a).getD (⊤,⊤)).2
  cases ht : p.trace a with
  | none =>
    change imageCondition r ≤ CertifiedStageLabel.admits Q ⊤
    rw [CertifiedStageLabel.admits_top]
    exact le_top
  | some s =>
    change imageCondition r ≤ CertifiedStageLabel.admits Q s.2
    exact ((historicalAdmission_cut old hab hP Q hQ p s).mp (p.valid a hab s ht)).2

theorem historicalCertifiedCondition_mono (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) :
    Monotone (historicalCertifiedCondition old hab hP Q hQ) := by
  intro p q hpq
  let F := historicalCertifiedCondition old hab hP Q hQ
  refine ⟨imageCondition_mono_r50 (historyCutPrefix_mono hab.le old hP hpq),?_⟩
  apply (staticValuedPoset_refines_iff _ _ _ (F p).nonzero _ _).mpr
  refine ⟨?_,(F p).valid⟩
  change ((p.trace a).getD (⊤,⊤)).2 ≤ ((q.trace a).getD (⊤,⊤)).2
  cases h : q.trace a with
  | none => exact le_top
  | some s =>
    obtain ⟨t,ht,hst⟩ := hpq a s h
    rw [ht]
    exact hst.2

theorem historicalCertifiedCondition_dense (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) (p : TotalCondition (certifiedQ Q)) :
    ∃ q : GoodPrefix old,historicalCertifiedCondition old hab hP Q hQ q ≤ p := by
  classical
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 p.mask p.nonzero
  have hd : imageCondition r ≤ CertifiedStageLabel.admits Q p.trace := hr.trans p.valid
  let t := attachHistoricalStep old hab succ Q hQ r p.trace hd
  let F := historicalCertifiedCondition old hab hP Q hQ
  have hm : (F t).mask = imageCondition r :=
    congrArg imageCondition (attachHistoricalStep_cut old hab hP succ Q hQ r p.trace hd)
  have ht : (F t).trace = p.trace := by
    change ((attachTrace r.trace a (⊤,p.trace) a).getD (⊤,⊤)).2 = p.trace
    simp [attachTrace]
  refine ⟨t,hm.trans_le hr,(staticValuedPoset_refines_iff _ _ _ (F t).nonzero _ _).mpr ?_⟩
  rw [hm,ht]
  exact ⟨le_rfl,hd⟩

theorem historicalCertifiedCondition_reflect (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) {p q : GoodPrefix old}
    (h : Compatible (historicalCertifiedCondition old hab hP Q hQ p)
      (historicalCertifiedCondition old hab hP Q hQ q)) : Compatible p q := by
  classical
  obtain ⟨w,hwp,hwq⟩ := h
  let C := historyCutPrefix hab.le old hP
  let F := historicalCertifiedCondition old hab hP Q hQ
  obtain ⟨r,hrp,hrq,hr⟩ := exists_common_prefix_below_r86
    (C p) (C q) w.nonzero hwp.1 hwq.1
  have hd : imageCondition r ≤ CertifiedStageLabel.admits Q w.trace := hr.trans w.valid
  let t := attachHistoricalStep old hab succ Q hQ r w.trace hd
  have hLe (u : GoodPrefix old) (hwu : w≤F u) (hru : r≤C u) : t≤u := by
    intro i s hs
    rcases lt_trichotomy i a with hi | he | hi
    · have hc : (C u).trace i = some s := (cut_apply_of_lt hi).trans hs
      obtain ⟨v,hv,hvs⟩ := hru i s hc
      refine ⟨v,?_,hvs⟩
      change attachTrace r.trace a (⊤,w.trace) i = some v
      simpa only [attachTrace,ite_eq_right hi.ne] using hv
    · subst i
      have hMask : s.1 = ⊤ :=
        ((historicalAdmission_cut old hab hP Q hQ u s).mp (u.valid a hab s hs)).1
      have hc := ((staticValuedPoset_refines_iff _ _ _ w.nonzero _ _).mp hwu.2).1
      change w.trace ≤ ((u.trace a).getD (⊤,⊤)).2 at hc
      rw [hs] at hc
      refine ⟨(⊤,w.trace),?_,⟨hMask.ge,hc⟩⟩
      change attachTrace r.trace a (⊤,w.trace) a = _
      simp [attachTrace]
    · exact False.elim (hi.not_ge ((succ i).mp (u.bounded i ⟨s,hs⟩)))
  exact ⟨t,hLe p hwp hrp,hLe q hwq hrq⟩

noncomputable def historicalStageComparison (old : StageHistory A B N b)
    (hab : a < b) (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) :
    DenseForcingMap (GoodPrefix old) (TotalCondition Q) :=
  denseForcingMap_comp930
    { map := historicalCertifiedCondition old hab hP Q hQ
      monotone := historicalCertifiedCondition_mono old hab hP Q hQ
      dense := historicalCertifiedCondition_dense old hab hP succ Q hQ
      reflect_compatible := fun h => historicalCertifiedCondition_reflect old hab hP succ Q hQ h }
    (certifiedHeadDenseMap Q)

end JSP000930.Negative
