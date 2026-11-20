import JSP000933TypedStageMap

namespace JSP000933
namespace FiniteSupport

variable {A T : Type} [LinearOrder A] [Preorder T]

def subHistory {a b : A} (hab : b ≤ a) (old : PrefixValidator a T) :
    PrefixValidator b T :=
  fun i hi => old i (hi.trans_le hab)

def HistoryPersistent {a : A} (old : PrefixValidator a T) : Prop :=
  ∀ i (hi : i < a) (p q : LabelTrace A T) (t : T),
    rawStronger (cut p i) (cut q i) → old i hi (cut q i) t → old i hi (cut p i) t

def partialHistoryRules {a : A} (old : PrefixValidator a T) (h : HistoryPersistent old) :
    Rules (fun (_ : A) => T) where
  valid := fun i p t => if hi : i < a then old i hi p t else False
  leAt := fun _ _ s t => s ≤ t
  refl := fun _ _ _ => le_rfl
  trans := fun _ _ _ _ _ huv hvw => huv.trans hvw
  persist_valid := by
    intro i p q t hpq hv
    by_cases hi : i < a
    · simp only [dite_eq_left hi] at hv ⊢
      exact h i hi p q t (rawStronger_cut_r84 i hpq) hv
    · simp only [dite_eq_right hi] at hv
  persist_le := fun _ _ _ _ _ _ hh => hh

theorem partialHistory_valid_iff_r131 {a : A} (old : PrefixValidator a T) (h : HistoryPersistent old)
    {i : A} (hi : i < a) (p : LabelTrace A T) (t : T) :
    (partialHistoryRules old h).valid i p t ↔ old i hi p t := by
  simp only [partialHistoryRules,dite_eq_left hi]

def partialHistoryPrefixIso_r131 {a b : A} (hab : b ≤ a)
    (old : PrefixValidator a T) (h : HistoryPersistent old) :
    Before (partialHistoryRules old h) b ≃o GoodPrefix (subHistory hab old) where
  toFun p := ⟨p.1.trace,p.1.finite,p.2,fun i hi s hs =>
    (partialHistory_valid_iff_r131 old h (hi.trans_le hab) _ s).mp (p.1.valid i s hs)⟩
  invFun p := ⟨⟨p.trace,p.finite,fun i s hi =>
    (partialHistory_valid_iff_r131 old h ((p.bounded i ⟨s,hi⟩).trans_le hab) _ s).mpr
      (p.valid i (p.bounded i ⟨s,hi⟩) s hi)⟩,p.bounded⟩
  left_inv := by
    rintro ⟨⟨trace,h1,h2⟩,h3⟩
    rfl
  right_inv := by
    rintro ⟨trace,h1,h2,h3⟩
    rfl
  map_rel_iff' := Iff.rfl

theorem earlierHistory_persistent_r131 [WellFoundedLT A] (policy : StagePolicy A T) (a : A) :
    HistoryPersistent (earlierValidated policy a) := by
  intro i hi p q s hpq h
  apply (localStageValid_unfold_r85 policy i (cut p i) s).mpr
  exact (rawProjection_mono_r84 (earlierValidated policy i) hpq).trans
    ((localStageValid_unfold_r85 policy i (cut q i) s).mp h)

end FiniteSupport
end JSP000933
