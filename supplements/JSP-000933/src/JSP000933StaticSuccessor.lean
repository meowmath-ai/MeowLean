import JSP000933RecursiveIteration
import JSP000933BooleanTwoStep

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion BooleanTwoStep

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T] [OrderTop T]
variable [DecidableRel ((· ≤ ·) : T → T → Prop)]
variable {B : Type} [CompleteBooleanAlgebra B]

def staticLabelStage (V : T → B) : Stage B T where
  admitted := V
  leVal := fun q r => if q ≤ r then ⊤ else ⊥
  reflVal q := by simp
  transVal q r s := by
    by_cases hqr : q ≤ r
    · by_cases hrs : r ≤ s
      · simp [hqr,hrs,hqr.trans hrs]
      · simp [hqr,hrs]
    · simp [hqr]

noncomputable abbrev StageOf (policy : StagePolicy A T) (a : A) :=
  staticLabelStage (policy a (earlierValidated policy a))

noncomputable def toStaticTwoStep (policy : StagePolicy A T) {a b : A}
    (hTop : policy a (earlierValidated policy a) (⊤ : T) = ⊤)
    (p : Before (iterationRules policy) b) : BooleanTwoStep.Condition (StageOf policy a) := by
  let q := typedRestrict policy p.1 a
  refine ⟨imageCondition q,(p.1.trace a).getD ⊤,imageCondition_ne_bot_r50 q,?_⟩
  change imageCondition q ≤ policy a (earlierValidated policy a) ((p.1.trace a).getD ⊤)
  cases ht : p.1.trace a with
  | none =>
    change imageCondition q ≤ policy a (earlierValidated policy a) (⊤ : T)
    rw [hTop] <;> exact le_top
  | some t =>
    exact (earlierStageValidity_iff_r85 policy p.1 a t).mp (p.1.valid a t ht)

theorem exists_common_prefix_below_r86 {P : Type} [Preorder P] (p q : P) {b : RO P}
    (hb : b ≠ ⊥) (hp : b ≤ imageCondition p) (hq : b ≤ imageCondition q) :
    ∃ r : P, r ≤ p ∧ r ≤ q ∧ imageCondition r ≤ b := by
  have hCompat (s t : P) (h : imageCondition s ≤ imageCondition t) : Compatible s t := by
    apply (compatible_iff_not_disjoint_r50 s t).mpr
    intro hd
    exact imageCondition_ne_bot_r50 s
      (le_bot_iff.mp ((le_inf le_rfl h).trans (disjoint_iff_inf_le.mp hd)))
  obtain ⟨s,hs⟩ := imageCondition_dense_r50 b hb
  obtain ⟨v,hvs,hvp⟩ := hCompat s p (hs.trans hp)
  have hv := (imageCondition_mono_r50 hvs).trans hs
  obtain ⟨r,hrv,hrq⟩ := hCompat v q (hv.trans hq)
  exact ⟨r,hrv.trans hvp,hrq,(imageCondition_mono_r50 hrv).trans hv⟩

def attachTrace (r : LabelTrace A T) (a : A) (t : T) : LabelTrace A T :=
  fun i => if i = a then some t else r i

theorem cut_attachTrace_of_le_r86 (r : LabelTrace A T) {a i : A} (h : i ≤ a) (t : T) :
    cut (attachTrace r a t) i = cut r i := by
  funext j
  by_cases hj : j < i
  · simp [cut,attachTrace,hj,(hj.trans_le h).ne]
  · simp [cut,hj]

theorem cut_eq_self_of_bounded_r86 {a : A} {r : LabelTrace A T}
    (h : ∀ i, present r i → i < a) : cut r a = r := by
  funext i
  by_cases hi : i < a
  · simp [cut,hi]
  · rw [cut_apply_of_not_lt hi]
    cases hr : r i with
    | none => rfl
    | some t => exact False.elim (hi (h i ⟨t,hr⟩))

noncomputable def attachCondition (policy : StagePolicy A T) {a b : A}
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (r : GoodPrefix (earlierValidated policy a)) (t : T)
    (hValid : imageCondition r ≤ policy a (earlierValidated policy a) t) :
    Before (iterationRules policy) b := by
  let m := attachTrace r.trace a t
  have hFin : ({i | present m i} : Set A).Finite := by
    apply ((Set.finite_singleton a).union r.finite).subset
    rintro i ⟨s,hs⟩
    by_cases hi : i = a
    · exact Or.inl hi
    · exact Or.inr ⟨s,by simpa [m,attachTrace,hi] using hs⟩
  have hBound (i : A) (hi : present m i) : i < b := by
    by_cases hia : i = a
    · exact (succ i).mpr hia.le
    · obtain ⟨s,hs⟩ := hi
      have hr : r.trace i = some s := by simpa [m,attachTrace,hia] using hs
      exact (succ i).mpr (r.bounded i ⟨s,hr⟩).le
  refine ⟨⟨m,hFin,?_⟩,hBound⟩
  intro i s hs
  change localStageValid policy i (cut m i) s
  have hle : i ≤ a := (succ i).mp (hBound i ⟨s,hs⟩)
  rw [cut_attachTrace_of_le_r86 r.trace hle t]
  by_cases hi : i = a
  · subst i
    have hts : t = s := by simpa [m,attachTrace] using hs
    subst s
    apply (localStageValid_unfold_r85 policy a (cut r.trace a) t).mpr
    rw [cut_eq_self_of_bounded_r86 r.bounded]
    change rawProjection (earlierValidated policy a) r.trace ≤ policy a (earlierValidated policy a) t
    rw [rawProjection_of_good_r84 _ r]
    exact hValid
  · have hr : r.trace i = some s := by simpa [m,attachTrace,hi] using hs
    exact r.valid i (r.bounded i ⟨s,hr⟩) s hr

end FiniteSupport
end JSP000933
