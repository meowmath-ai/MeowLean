import JSP000933MaskRealization
import JSP000933StaticSuccessor

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

abbrev BasedLabel (B T : Type) := B × T

abbrev BasedTailPolicy (A B T : Type) [LinearOrder A] [CompleteBooleanAlgebra B]
    [Preorder T] :=
  (a : A) → (old : PrefixValidator a (BasedLabel B T)) → T → RO (GoodPrefix old)

noncomputable def basedPolicy (tail : BasedTailPolicy A B T) :
    StagePolicy A (BasedLabel B T) := by
  classical
  intro a old t
  exact if a = ⊥ then
    if t.1 ≠ ⊥ ∧ t.2 = ⊤ then ⊤ else ⊥
  else
    if t.1 = ⊤ then tail a old t.2 else ⊥

abbrev BasedCondition (tail : BasedTailPolicy A B T) :=
  IterationCondition (basedPolicy tail)

theorem basedPolicy_stage_top (tail : BasedTailPolicy A B T)
    (h : ∀ a old, tail a old ⊤ = ⊤) (a : A)
    (old : PrefixValidator a (BasedLabel B T)) :
    basedPolicy tail a old (⊤ : BasedLabel B T) = ⊤ := by
  classical
  by_cases ha : a = ⊥
  · simp [basedPolicy, ha, top_ne_bot]
  · simp [basedPolicy, ha, h]

theorem rawProjection_none_top {a : A} (old : PrefixValidator a (BasedLabel B T)) :
    rawProjection old (fun _ => none) = ⊤ := by
  apply top_unique
  by_contra hn
  have hN : (rawProjection old (fun _ => none))ᶜ ≠ ⊥ := fun he =>
    hn (compl_eq_bot.mp he).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
  have hQ : imageCondition p ≤ rawProjection old (fun _ => none) :=
    le_iSup (fun q : {q : GoodPrefix old // rawStronger q.trace (fun _ => none)} => imageCondition q.val)
      ⟨p, fun _ _ he => by cases he⟩
  exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _ hQ hp)

theorem basedPolicy_min_valid (tail : BasedTailPolicy A B T)
    (p : LabelTrace A (BasedLabel B T)) (t : BasedLabel B T) :
    localStageValid (basedPolicy tail) (⊥ : A) (cut p ⊥) t ↔ t.1 ≠ ⊥ ∧ t.2 = ⊤ := by
  classical
  have he : cut p (⊥ : A) = fun _ => none := by
    funext j
    exact cut_apply_of_not_lt (not_lt_of_ge bot_le)
  rw [localStageValid_unfold_r85, he, rawProjection_none_top]
  let P := GoodPrefix (earlierValidated (basedPolicy tail) (⊥ : A))
  let p0 : P := {
    trace := fun _ => none
    finite := by simp [present]
    bounded := fun _ ⟨s,hs⟩ => by cases hs
    valid := fun _ _ _ h => by cases h }
  have hRO : (⊤ : RO P) ≠ ⊥ := fun he =>
    imageCondition_ne_bot_r50 p0 (le_bot_iff.mp (le_top.trans_eq he))
  by_cases h : t.1 ≠ ⊥ ∧ t.2 = ⊤
  · simp [basedPolicy,h]
  · simp only [basedPolicy, ite_true, h, ite_false, top_le_iff, iff_false]
    exact Ne.symm hRO

theorem basedPolicy_tail_admission (tail : BasedTailPolicy A B T)
    {a : A} (ha : a ≠ ⊥) (old : PrefixValidator a (BasedLabel B T)) (s : T) :
    basedPolicy tail a old (⊤,s) = tail a old s := by
  classical
  simp [basedPolicy,ha]

def baseMask (tail : BasedTailPolicy A B T) (p : BasedCondition tail) : B :=
  ((p.trace ⊥).getD (⊤,⊤)).1

theorem baseMask_positive (tail : BasedTailPolicy A B T) (p : BasedCondition tail) :
    baseMask tail p ≠ ⊥ := by
  cases hp : p.trace ⊥ with
  | none => simpa [baseMask,hp] using (top_ne_bot : (⊤ : B) ≠ ⊥)
  | some s =>
    simpa only [baseMask,hp,Option.getD_some] using
      ((basedPolicy_min_valid tail p.trace s).mp (p.valid ⊥ s hp)).1

theorem baseMask_mono (tail : BasedTailPolicy A B T) :
    Monotone (baseMask tail) := by
  intro p q hpq
  cases hq : q.trace ⊥ with
  | none => simp [baseMask,hq]
  | some s =>
    obtain ⟨t,ht,h⟩ := hpq (⊥ : A) s hq
    simpa only [baseMask,hq,ht,Option.getD_some] using h.1

noncomputable def basedEmpty (tail : BasedTailPolicy A B T) : BasedCondition tail where
  trace := fun _ => none
  finite := by simp [present]
  valid := fun _ _ h => by cases h

theorem baseMask_empty (tail : BasedTailPolicy A B T) :
    baseMask tail (basedEmpty tail) = ⊤ := rfl

noncomputable def putBase (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    (b : B) (hb : b ≠ ⊥) (hle : b ≤ baseMask tail p) : BasedCondition tail := by
  let q := attachTrace p.trace (⊥ : A) ((b,⊤) : BasedLabel B T)
  have hRaw : rawStronger q p.trace := by
    intro j s hs
    by_cases hj : j = ⊥
    · subst j
      have hsTop := ((basedPolicy_min_valid tail p.trace s).mp (p.valid ⊥ s hs)).2
      refine ⟨(b,⊤),by simp [q,attachTrace],?_⟩
      refine ⟨?_,by rw [hsTop] <;> exact le_rfl⟩
      simpa only [baseMask,hs,Option.getD_some] using hle
    · exact ⟨s,by simp [q,attachTrace,hj,hs],le_rfl⟩
  refine ⟨q,?_,?_⟩
  · apply ((Set.finite_singleton (⊥ : A)).union p.finite).subset
    rintro j ⟨s,hs⟩
    by_cases hj : j = ⊥
    · exact Or.inl hj
    · exact Or.inr ⟨s,by simpa [q,attachTrace,hj] using hs⟩
  · intro j s hs
    by_cases hj : j = ⊥
    · subst j
      have hS : ((b,⊤) : BasedLabel B T) = s := by simpa [q,attachTrace] using hs
      subst s
      exact (basedPolicy_min_valid tail q (b,⊤)).mpr ⟨hb,rfl⟩
    · have hS : p.trace j = some s := by simpa [q,attachTrace,hj] using hs
      exact (iterationRules (basedPolicy tail)).persist_valid j q p.trace s
        (fun i _ => hRaw i) (p.valid j s hS)

theorem putBase_le (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    (b : B) (hb : b ≠ ⊥) (hle : b ≤ baseMask tail p) :
    putBase tail p b hb hle ≤ p := by
  intro j s hs
  by_cases hj : j = ⊥
  · subst j
    have ht := ((basedPolicy_min_valid tail p.trace s).mp (p.valid ⊥ s hs)).2
    refine ⟨(b,⊤),by simp [putBase,attachTrace],?_⟩
    exact ⟨by simpa only [baseMask,hs,Option.getD_some] using hle,
      by rw [ht] <;> exact le_rfl⟩
  · exact ⟨s,by simp [putBase,attachTrace,hj,hs],le_rfl⟩

theorem putBase_mask (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    (b : B) (hb : b ≠ ⊥) (hle : b ≤ baseMask tail p) :
    baseMask tail (putBase tail p b hb hle) = b := by
  simp [baseMask,putBase,attachTrace]

noncomputable def basedMaskRealization (tail : BasedTailPolicy A B T) :
    MaskRealization B (BasedCondition tail) where
  mask := baseMask tail
  positive := baseMask_positive tail
  monotone := baseMask_mono tail
  realizes b hb := by
    have hle : b ≤ baseMask tail (basedEmpty tail) := le_top
    exact ⟨putBase tail (basedEmpty tail) b hb hle,putBase_mask tail _ b hb hle⟩
  cut p b hb := by
    let c := baseMask tail p ⊓ b
    exact ⟨putBase tail p c hb inf_le_left,putBase_le tail p c hb inf_le_left,
      putBase_mask tail p c hb inf_le_left⟩

noncomputable def basedBaseEmbed (tail : BasedTailPolicy A B T) :
    CompleteValueMap B (RO (BasedCondition tail)) := by
  letI : Nonempty (BasedCondition tail) := ⟨basedEmpty tail⟩
  exact (basedMaskRealization tail).completeValueMap

end ForcingTransport
end JSP000933
