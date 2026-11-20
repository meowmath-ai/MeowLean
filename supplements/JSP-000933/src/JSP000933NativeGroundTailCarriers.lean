import JSP000933RawTailQuotientComparison

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion MarkedForcing FiniteSupport RelativeOCA OpenGraphForcing

structure RawTail {A : Type} (T : Type) (allowed : A → Prop) where
  trace : LabelTrace A T
  finite : ({i | present trace i} : Set A).Finite
  bounded : ∀ i, present trace i → allowed i

namespace RawTail

variable {A T : Type} {allowed : A→Prop}

instance [LinearOrder A] [Preorder T] : Preorder (RawTail T allowed) where
  le p q := rawStronger p.trace q.trace
  le_refl p := rawStronger_refl_r84 p.trace
  le_trans _ _ _ := rawStronger_trans_r84

def empty : RawTail T allowed := ⟨fun _ => none,by simp [present],by
  rintro i ⟨s,h⟩
  cases h⟩

instance [LinearOrder A] [Preorder T] : OrderTop (RawTail T allowed) where
  top := empty
  le_top p := by intro i s h; cases h

theorem extTrace {p q : RawTail T allowed} (h : p.trace=q.trace) : p=q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def scope (r : RawTail T allowed) : Finset A := r.finite.toFinset

@[simp] theorem mem_scope (r : RawTail T allowed) (i : A) :
    i∈r.scope ↔ present r.trace i := r.finite.mem_toFinset

end RawTail

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

noncomputable def stripBaseTrace (p : LabelTrace A (BasedLabel B T)) : LabelTrace A T :=
  fun i => if i=⊥ then none else (p i).map Prod.snd

theorem stripBaseTrace_present (p : LabelTrace A (BasedLabel B T)) {i : A}
    (h : present (stripBaseTrace p) i) : i≠⊥ ∧ present p i := by
  obtain ⟨s,hs⟩ := h
  by_cases hi : i=⊥
  · simp [stripBaseTrace,hi] at hs
  · refine ⟨hi,?_⟩
    cases he : p i with
    | none => simp [stripBaseTrace,hi,he] at hs
    | some t => exact ⟨t,he⟩

noncomputable def stripBase (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    (allowed : A→Prop) (h : ∀ i, present p.trace i → allowed i) : RawTail T allowed where
  trace := stripBaseTrace p.trace
  finite := p.finite.subset (fun _ hi => (stripBaseTrace_present _ hi).2)
  bounded := fun i hi => h i (stripBaseTrace_present _ hi).2

theorem stripBaseTrace_mono
    {p q : LabelTrace A (BasedLabel B T)} (h : rawStronger p q) :
    rawStronger (stripBaseTrace p) (stripBaseTrace q) := by
  intro i s hs
  by_cases hi : i=⊥
  · simp [stripBaseTrace,hi] at hs
  · cases hq : q i with
    | none => simp [stripBaseTrace,hi,hq] at hs
    | some t =>
      have hts : t.2=s := by simpa [stripBaseTrace,hi,hq] using hs
      obtain ⟨u,hu,hut⟩ := h i t hq
      exact ⟨u.2,by simp [stripBaseTrace,hi,hu],hut.2.trans_eq hts⟩

theorem stripBaseTrace_putBase (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    (b : B) (hb : b≠⊥) (hle : b≤baseMask tail p) :
    stripBaseTrace (putBase tail p b hb hle).trace = stripBaseTrace p.trace := by
  funext i
  by_cases hi : i=⊥ <;> simp [stripBaseTrace,putBase,attachTrace,hi]

theorem putBase_le_of_comparison (tail : BasedTailPolicy A B T) (p q : BasedCondition tail)
    (b : B) (hb : b≠⊥) (hle : b≤baseMask tail p) (hbq : b≤baseMask tail q)
    (hTail : rawStronger (stripBaseTrace p.trace) (stripBaseTrace q.trace)) :
    putBase tail p b hb hle ≤ q := by
  intro i s hs
  by_cases hi : i=⊥
  · subst i
    have hsTop := ((basedPolicy_min_valid tail q.trace s).mp (q.valid ⊥ s hs)).2
    refine ⟨(b,⊤),by simp [putBase,attachTrace],?_⟩
    exact ⟨by simpa only [baseMask,hs,Option.getD_some] using hbq,by rw [hsTop]⟩
  · have hs' : stripBaseTrace q.trace i=some s.2 := by simp [stripBaseTrace,hi,hs]
    obtain ⟨t,ht,hts⟩ := hTail i s.2 hs'
    cases he : p.trace i with
    | none => simp [stripBaseTrace,hi,he] at ht
    | some u =>
      have hut : u.2=t := by simpa [stripBaseTrace,hi,he] using ht
      have hU := actualTailLabel_hasTopMask tail hi p u he
      have hS := actualTailLabel_hasTopMask tail hi q s hs
      refine ⟨u,by simp [putBase,attachTrace,hi,he],?_⟩
      exact ⟨by rw [hU,hS],hut.trans_le hts⟩

abbrev WholeTail (A T : Type) := RawTail T (fun _ : A => True)
abbrev PrefixTail {A : Type} [LT A] (a : A) (T : Type) := RawTail T (fun i => i<a)

noncomputable def wholeTailPresentation (tail : BasedTailPolicy A B T) :
    TailPresentation (N := WholeTail A T) (basedMaskRealization tail) where
  strip p := stripBase tail p _ (fun _ _ => trivial)
  mono_strip := fun _ _ h => stripBaseTrace_mono h
  empty := basedEmpty tail
  empty_mask := baseMask_empty tail
  empty_strip := by
    apply RawTail.extTrace
    funext i
    change (stripBaseTrace _ i) = none
    simp [stripBase,stripBaseTrace,basedEmpty,RawTail.empty]
  replace := putBase tail
  replace_mask := putBase_mask tail
  replace_strip := by
    intro p b hb hle
    apply RawTail.extTrace
    exact stripBaseTrace_putBase tail p b hb hle
  replace_le_of := putBase_le_of_comparison tail

noncomputable def prefixTailPresentation (tail : BasedTailPolicy A B T) {a : A} (ha : (⊥ : A)<a) :
    TailPresentation (N := PrefixTail a T) (prefixMaskRealization tail ha) where
  strip p := stripBase tail p.val _ p.property
  mono_strip := fun _ _ h => stripBaseTrace_mono h
  empty := basedEmptyBefore tail a
  empty_mask := baseMask_empty tail
  empty_strip := by
    apply RawTail.extTrace
    funext i
    change (stripBaseTrace _ i) = none
    simp [stripBase,stripBaseTrace,basedEmptyBefore,basedEmpty,RawTail.empty]
  replace p b hb hle := ⟨putBase tail p.val b hb hle,putBase_bounded tail ha p b hb hle⟩
  replace_mask p b hb hle := putBase_mask tail p.val b hb hle
  replace_strip := by
    intro p b hb hle
    apply RawTail.extTrace
    exact stripBaseTrace_putBase tail p.val b hb hle
  replace_le_of p q b hb hle hbq hTail := putBase_le_of_comparison tail p.val q.val b hb hle hbq hTail

end ForcingTransport
end JSP000933
