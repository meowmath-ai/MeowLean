import JSP000933FiniteSupportAmalgamation

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {A T : Type} [LinearOrder A] [Preorder T]

abbrev LabelTrace (A T : Type) := Trace (fun (_ : A) => T)

def rawStronger (p q : LabelTrace A T) : Prop :=
  ∀ i (s : T), q i = some s → ∃ t : T, p i = some t ∧ t ≤ s

theorem rawStronger_refl_r84 (p : LabelTrace A T) : rawStronger p p :=
  fun _ s hs => ⟨s,hs,le_rfl⟩

theorem rawStronger_trans_r84 {p q r : LabelTrace A T}
    (hpq : rawStronger p q) (hqr : rawStronger q r) : rawStronger p r := by
  intro i s hs
  obtain ⟨t,ht,hts⟩ := hqr i s hs
  obtain ⟨v,hv,hvt⟩ := hpq i t ht
  exact ⟨v,hv,hvt.trans hts⟩

theorem rawStronger_cut_r84 {p q : LabelTrace A T} (a : A)
    (h : ∀ i < a, ∀ s : T, q i = some s → ∃ t : T, p i = some t ∧ t ≤ s) :
    rawStronger (cut p a) (cut q a) := by
  intro i s hs
  by_cases hi : i < a
  · obtain ⟨t,ht,hts⟩ := h i hi s (by simpa [cut,hi] using hs)
    exact ⟨t,by simpa [cut,hi] using ht,hts⟩
  · simp [cut,hi] at hs

abbrev PrefixValidator (a : A) (T : Type) :=
  (i : A) → i < a → LabelTrace A T → T → Prop

structure GoodPrefix {a : A} (localValid : PrefixValidator a T) where
  trace : LabelTrace A T
  finite : ({i | present trace i} : Set A).Finite
  bounded : ∀ i, present trace i → i < a
  valid : ∀ i (hi : i < a) (s : T), trace i = some s → localValid i hi (cut trace i) s

instance {a : A} (localValid : PrefixValidator a T) : Preorder (GoodPrefix localValid) where
  le p q := rawStronger p.trace q.trace
  le_refl p := rawStronger_refl_r84 p.trace
  le_trans _ _ _ := rawStronger_trans_r84

noncomputable def rawProjection {a : A} (localValid : PrefixValidator a T)
    (p : LabelTrace A T) : RO (GoodPrefix localValid) :=
  ⨆ q : {q : GoodPrefix localValid // rawStronger q.trace p}, imageCondition q.1

theorem rawProjection_mono_r84 {a : A} (localValid : PrefixValidator a T)
    {p q : LabelTrace A T} (h : rawStronger p q) :
    rawProjection localValid p ≤ rawProjection localValid q := by
  apply iSup_le
  rintro ⟨r,hr⟩
  exact le_iSup
    (fun s : {s : GoodPrefix localValid // rawStronger s.trace q} => imageCondition s.1)
    ⟨r,rawStronger_trans_r84 hr h⟩

theorem rawProjection_of_good_r84 {a : A} (localValid : PrefixValidator a T)
    (p : GoodPrefix localValid) :
    rawProjection localValid p.trace = imageCondition p := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨q,hq⟩
    exact imageCondition_mono_r50 (show q ≤ p from hq)
  · exact le_iSup (fun s : {s : GoodPrefix localValid // rawStronger s.trace p.trace} =>
      imageCondition s.1) ⟨p,rawStronger_refl_r84 p.trace⟩

end FiniteSupport
end JSP000933
