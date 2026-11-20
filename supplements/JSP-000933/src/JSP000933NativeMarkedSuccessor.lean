import JSP000933DenseForcingMap
import JSP000933MarkedTotalForcing

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion MarkedForcing FiniteSupport

section StaticIterand
variable {B T : Type} [CompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

noncomputable def staticValuedPoset (V : T → B) (hV : Monotone V) (hTop : V ⊤ = ⊤) :
    ValuedPoset B T := by
  classical
  refine ⟨V,fun n m => if n≤ m then V n else ⊥,?_,?_,?_,⊤,hTop,?_⟩
  · intro n m
    by_cases h : n≤ m
    · rw [ite_eq_left h]; exact le_inf le_rfl (hV h)
    · rw [ite_eq_right h]; exact bot_le
  · intro n
    rw [ite_eq_left le_rfl]
  · intro n m k
    by_cases hnm : n≤ m
    · by_cases hmk : m≤k
      · simp only [ite_eq_left hnm,ite_eq_left hmk,ite_eq_left (hnm.trans hmk)]
        exact inf_le_left
      · simp only [ite_eq_right hmk,inf_bot_eq,bot_le]
    · simp only [ite_eq_right hnm,bot_inf_eq,bot_le]
  · intro n
    rw [ite_eq_left le_top]

theorem staticValuedPoset_refines_iff (V : T → B) (hV : Monotone V) (hTop : V ⊤ = ⊤)
    {b : B} (hb : b ≠ ⊥) (n m : T) :
    b ≤ (staticValuedPoset V hV hTop).refines n m ↔ n≤ m ∧ b≤V n := by
  classical
  change (b ≤ if n≤ m then V n else ⊥) ↔ _
  by_cases h : n≤ m
  · simp only [h,ite_true,true_and]
  · simp only [ite_eq_right h,h,false_and]
    exact ⟨fun k => hb (le_bot_iff.mp k),False.elim⟩

end StaticIterand

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

variable (tail : BasedTailPolicy A B T) {a b : A} (ha : a ≠ ⊥)

abbrev PreStageAlgebra := RO (GoodPrefix (earlierValidated (basedPolicy tail) a))

abbrev TailStageValues : T → PreStageAlgebra tail (a := a) :=
  tail a (earlierValidated (basedPolicy tail) a)

variable (hVa : Monotone (TailStageValues tail (a := a)))
  (hTop : TailStageValues tail (a := a) ⊤ = ⊤)

noncomputable abbrev ExactTailIterand := staticValuedPoset (TailStageValues tail (a := a)) hVa hTop

include ha in
theorem actualTailLabel_hasTopMask (p : BasedCondition tail) (s : BasedLabel B T)
    (hs : p.trace a = some s) : s.1 = ⊤ := by
  classical
  by_contra hn
  have hE := (earlierStageValidity_iff_r85 (basedPolicy tail) p a s).mp (p.valid a s hs)
  have hBot : basedPolicy tail a (earlierValidated (basedPolicy tail) a) s = ⊥ := by
    simp [basedPolicy,ha,hn]
  rw [hBot] at hE
  exact imageCondition_ne_bot_r50 _ (le_bot_iff.mp hE)

include ha in
noncomputable def toMarkedSuccessor (p : BasedBefore tail b) :
    TotalCondition (ExactTailIterand tail hVa hTop) where
  mask := imageCondition (typedRestrict (basedPolicy tail) p.val a)
  trace := ((p.val.trace a).getD (⊤,⊤)).2
  nonzero := imageCondition_ne_bot_r50 _
  valid := by
    change imageCondition (typedRestrict (basedPolicy tail) p.val a) ≤
      TailStageValues tail (a := a) ((p.val.trace a).getD (⊤,⊤)).2
    cases hs : p.val.trace a with
    | none =>
      change imageCondition (typedRestrict (basedPolicy tail) p.val a) ≤
        TailStageValues tail (a := a) ⊤
      rw [hTop]
      exact le_top
    | some s =>
      have ht := actualTailLabel_hasTopMask tail ha p.val s hs
      have hE := (earlierStageValidity_iff_r85 (basedPolicy tail) p.val a s).mp (p.val.valid a s hs)
      rcases s with ⟨u,v⟩
      change u = ⊤ at ht
      subst u
      rw [basedPolicy_tail_admission tail ha] at hE
      exact hE

theorem toMarkedSuccessor_mono :
    Monotone (toMarkedSuccessor tail ha hVa hTop (b := b)) := by
  intro p q hpq
  let P := toMarkedSuccessor tail ha hVa hTop p
  let Q := toMarkedSuccessor tail ha hVa hTop q
  have hM : P.mask ≤ Q.mask :=
    imageCondition_mono_r50
      ((prefixOrderIso_r85 (basedPolicy tail) a).monotone (restrict_mono_r75 hpq a))
  have hT : P.trace ≤ Q.trace := by
    change ((p.val.trace a).getD (⊤,⊤)).2 ≤ ((q.val.trace a).getD (⊤,⊤)).2
    cases hq : q.val.trace a with
    | none => exact le_top
    | some s =>
      obtain ⟨t,ht,h⟩ := hpq a s hq
      rw [ht]
      exact h.2
  exact ⟨hM,(staticValuedPoset_refines_iff _ hVa hTop P.nonzero _ _).mpr ⟨hT,P.valid⟩⟩

theorem goodPrefix_eq_of_trace {α : A} {old : PrefixValidator α (BasedLabel B T)}
    (p q : GoodPrefix old) (h : p.trace = q.trace) : p = q := by
  cases p
  cases q
  cases h
  rfl

open Classical in
theorem typedRestrict_attach_self
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (r : GoodPrefix (earlierValidated (basedPolicy tail) a)) (s : T)
    (hV : imageCondition r ≤ TailStageValues tail (a := a) s) :
    let c := attachCondition (basedPolicy tail) succ r (⊤,s)
      (hV.trans_eq (basedPolicy_tail_admission tail ha _ s).symm)
    typedRestrict (basedPolicy tail) c.val a = r := by
  dsimp only
  apply goodPrefix_eq_of_trace
  change cut (attachTrace r.trace a (⊤,s)) a = r.trace
  rw [cut_attachTrace_of_le_r86 _ le_rfl,cut_eq_self_of_bounded_r86 r.bounded]

theorem toMarkedSuccessor_dense (succ : ∀ i : A, i < b ↔ i ≤ a)
    (s : TotalCondition (ExactTailIterand tail hVa hTop)) :
    ∃ p : BasedBefore tail b, toMarkedSuccessor tail ha hVa hTop p ≤ s := by
  classical
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 s.mask s.nonzero
  have hV : imageCondition r ≤ TailStageValues tail (a := a) s.trace := hr.trans s.valid
  let c := attachCondition (basedPolicy tail) succ r (⊤,s.trace)
    (hV.trans_eq (basedPolicy_tail_admission tail ha _ s.trace).symm)
  let u := toMarkedSuccessor tail ha hVa hTop c
  have hM : u.mask = imageCondition r :=
    congrArg imageCondition (typedRestrict_attach_self tail ha succ r _ hV)
  have hT : u.trace = s.trace := by
    change ((attachTrace r.trace a (⊤,s.trace) a).getD (⊤,⊤)).2 = _
    simp [attachTrace]
  refine ⟨c, hM.trans_le hr, (staticValuedPoset_refines_iff _ hVa hTop u.nonzero _ _).mpr ?_⟩
  rw [hT,hM]
  exact ⟨le_rfl,hV⟩

theorem toMarkedSuccessor_compatible (succ : ∀ i : A, i < b ↔ i ≤ a)
    (p q : BasedBefore tail b)
    (h : Compatible (toMarkedSuccessor tail ha hVa hTop p)
       (toMarkedSuccessor tail ha hVa hTop q)) : Compatible p q := by
  classical
  obtain ⟨w,hwp,hwq⟩ := h
  obtain ⟨r,hrp,hrq,hr⟩ := exists_common_prefix_below_r86
    (typedRestrict (basedPolicy tail) p.val a) (typedRestrict (basedPolicy tail) q.val a)
    w.nonzero hwp.1 hwq.1
  have hV : imageCondition r ≤ TailStageValues tail (a := a) w.trace := hr.trans w.valid
  let c := attachCondition (basedPolicy tail) succ r (⊤,w.trace)
    (hV.trans_eq (basedPolicy_tail_admission tail ha _ w.trace).symm)
  have hLe (z : BasedBefore tail b) (hwz : w ≤ toMarkedSuccessor tail ha hVa hTop z)
      (hrz : r ≤ typedRestrict (basedPolicy tail) z.val a) : c≤z := by
    change ∀ i (s : BasedLabel B T), z.val.trace i = some s →
      ∃ t : BasedLabel B T, attachTrace r.trace a (⊤,w.trace) i = some t ∧ t ≤ s
    intro i s hs
    rcases lt_trichotomy i a with hi | he | hi
    · have hCut : (typedRestrict (basedPolicy tail) z.val a).trace i = some s :=
        (cut_apply_of_lt hi).trans hs
      obtain ⟨t,ht,hte⟩ := hrz i s hCut
      exact ⟨t,by simpa [attachTrace,hi.ne] using ht,hte⟩
    · subst i
      have hMask := actualTailLabel_hasTopMask tail ha z.val s hs
      have ht := ((staticValuedPoset_refines_iff _ hVa hTop w.nonzero _ _).mp hwz.2).1
      have ht' : w.trace ≤ s.2 := by
        change w.trace ≤ ((z.val.trace a).getD (⊤,⊤)).2 at ht
        rwa [hs] at ht
      refine ⟨(⊤,w.trace),by simp [attachTrace],?_⟩
      exact ⟨by rw [hMask] <;> exact le_rfl,ht'⟩
    · exact False.elim (hi.not_ge ((succ i).mp (z.property i ⟨s,hs⟩)))
  exact ⟨c,hLe p hwp hrp,hLe q hwq hrq⟩

noncomputable def markedSuccessorComparison (succ : ∀ i : A, i < b ↔ i ≤ a) :
    DenseForcingMap (BasedBefore tail b) (TotalCondition (ExactTailIterand tail hVa hTop)) where
  map := toMarkedSuccessor tail ha hVa hTop
  monotone := toMarkedSuccessor_mono tail ha hVa hTop
  dense := toMarkedSuccessor_dense tail ha hVa hTop succ
  reflect_compatible := fun h => toMarkedSuccessor_compatible tail ha hVa hTop succ _ _ h

end ForcingTransport
end JSP000933
