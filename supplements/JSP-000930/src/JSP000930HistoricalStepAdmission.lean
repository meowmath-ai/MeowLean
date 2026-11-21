import JSP000930FixedWetzelReadyBook

namespace JSP000930.Negative

open JSP000933.FiniteSupport JSP000933.ForcingTransport JSP000933.BooleanCompletion
open JSP000933.MarkedForcing

variable {A B N : Type} [LinearOrder A] [WellFoundedLT A]
  [CompleteBooleanAlgebra B] {a b : A}

abbrev StageHistory (A B N : Type) [LinearOrder A] [CompleteBooleanAlgebra B]
    (j : A) := PrefixValidator j (BasedLabel B (CertifiedStageLabel N))

abbrev HistoryPrefixAlgebra (old : StageHistory A B N b) (hab : a ≤ b) :=
  RO (GoodPrefix (subHistory hab old))

def HistoricalAdmission (old : StageHistory A B N b) (hab : a < b)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N) : Prop :=
  ∀ (p : GoodPrefix (subHistory hab.le old)) (s : BasedLabel B (CertifiedStageLabel N)),
    old a hab p.trace s ↔ s.1 = ⊤ ∧
      imageCondition p ≤ CertifiedStageLabel.admits Q s.2

theorem historicalAdmission_cut (old : StageHistory A B N b) (hab : a < b)
    (hP : HistoryPersistent old) (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q) (p : GoodPrefix old)
    (s : BasedLabel B (CertifiedStageLabel N)) :
    old a hab (cut p.trace a) s ↔ s.1 = ⊤ ∧
      imageCondition (historyCutPrefix hab.le old hP p) ≤ CertifiedStageLabel.admits Q s.2 := by
  rw [← historyCutPrefix_trace hab.le old hP p]
  exact hQ _ s

noncomputable def attachHistoricalStep (old : StageHistory A B N b) (hab : a < b)
    (succ : ∀ i : A,i<b ↔ i≤a) (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q)
    (r : GoodPrefix (subHistory hab.le old)) (t : CertifiedStageLabel N)
    (ht : imageCondition r ≤ CertifiedStageLabel.admits Q t) : GoodPrefix old := by
  classical
  let m := attachTrace r.trace a (⊤,t)
  have hF : ({i | present m i} : Set A).Finite := by
    apply ((Set.finite_singleton a).union r.finite).subset
    intro i hi
    obtain ⟨s,hs⟩ := hi
    by_cases he : i = a
    · exact Or.inl he
    · exact Or.inr ⟨s,by simpa [m,attachTrace,he] using hs⟩
  have hB (i : A) (hi : present m i) : i < b := by
    apply (succ i).mpr
    by_cases he : i=a
    · exact he.le
    · obtain ⟨s,hs⟩ := hi
      have hv : r.trace i = some s := by simpa [m,attachTrace,he] using hs
      exact (r.bounded i ⟨s,hv⟩).le
  refine ⟨m,hF,hB,?_⟩
  intro i hi s hs
  have hil : i≤a := (succ i).mp hi
  change old i hi (cut m i) s
  rw [cut_attachTrace_of_le_r86 r.trace hil (⊤,t)]
  by_cases he : i = a
  · subst i
    have hts : (⊤,t) = s := by simpa [m,attachTrace] using hs
    subst s
    rw [cut_eq_self_of_bounded_r86 r.bounded]
    exact (hQ r _).mpr ⟨rfl,ht⟩
  · have hv : r.trace i = some s := by simpa [m,attachTrace,he] using hs
    exact r.valid i (hil.lt_of_ne he) s hv

theorem attachHistoricalStep_cut (old : StageHistory A B N b) (hab : a < b)
    (hP : HistoryPersistent old) (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (HistoryPrefixAlgebra old hab.le) N)
    (hQ : HistoricalAdmission old hab Q)
    (r : GoodPrefix (subHistory hab.le old)) (t : CertifiedStageLabel N)
    (ht : imageCondition r ≤ CertifiedStageLabel.admits Q t) :
    historyCutPrefix hab.le old hP (attachHistoricalStep old hab succ Q hQ r t ht) = r := by
  classical
  apply goodPrefix_eq_of_trace930
  change cut (attachTrace r.trace a (⊤,t)) a = r.trace
  rw [cut_attachTrace_of_le_r86 _ le_rfl,cut_eq_self_of_bounded_r86 r.bounded]

end JSP000930.Negative
