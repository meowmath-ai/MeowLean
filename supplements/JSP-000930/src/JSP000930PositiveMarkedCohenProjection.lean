import JSP000930PositiveCohenBlockProjection

namespace JSP000930.Positive.Cohen

open JSP000933.MarkedForcing

variable {B X : Type} [CompleteBooleanAlgebra B]

abbrev CohenTotal (B X : Type) [CompleteBooleanAlgebra B] :=
  TotalCondition (valuedCohen B X)

abbrev BlockTotal (B : Type) [CompleteBooleanAlgebra B] (S : Set X) :=
  {p : CohenTotal B X // Supported p.trace S}

noncomputable def restrictTotal (p : CohenTotal B X) (S : Set X) : BlockTotal B S :=
  ⟨⟨p.mask, (restrict p.trace S).1, p.nonzero, le_top⟩, (restrict p.trace S).2⟩

theorem restrictTotal_mono (S : Set X) :
    Monotone (fun p : CohenTotal B X => restrictTotal p S) := by
  intro p q hpq
  have h := (cohen_total_le_iff p q).mp hpq
  change (restrictTotal p S).1 ≤ (restrictTotal q S).1
  exact (cohen_total_le_iff _ _).mpr ⟨h.1, restrict_monotone S h.2⟩

theorem lift_stronger_total_block (p : CohenTotal B X)
    (S : Set X) (q : BlockTotal B S)
    (hq : q ≤ restrictTotal p S) :
    ∃ r : CohenTotal B X, r ≤ p ∧ r ≤ q.1 := by
  change q.1 ≤ (restrictTotal p S).1 at hq
  obtain ⟨hm,ht⟩ := (cohen_total_le_iff _ _).mp hq
  obtain ⟨t,hp,hqt⟩ := lift_stronger_block p.trace S ⟨q.1.trace,q.2⟩ ht
  let r : CohenTotal B X := ⟨q.1.mask,t,q.1.nonzero,le_top⟩
  exact ⟨r,(cohen_total_le_iff _ _).mpr ⟨hm,hp⟩,
    (cohen_total_le_iff _ _).mpr ⟨le_rfl,hqt⟩⟩

end JSP000930.Positive.Cohen
