import JSP000930NegativeInertRelativeCCC
import JSP000930RegularOpenPredensity

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B N M : Type} [CompleteBooleanAlgebra B]

abbrev MaskedCondition (Q : ValuedPoset B N) (m : B) :=
  {p : TotalCondition Q // p.mask ≤ m}

structure LocalTraceInclusion (Q : ValuedPoset B N) (R : ValuedPoset B M) (m : B) where
  label : N → M
  valid : ∀ t,m ⊓ R.valid (label t) = m ⊓ Q.valid t
  refines : ∀ t u,m ⊓ R.refines (label t) (label u) = m ⊓ Q.refines t u
  reflectCommon : ∀ t u,m ⊓ commonRefinementValue R (label t) (label u) ≤
    m ⊓ commonRefinementValue Q t u

theorem inertOutside_eq_of_clip (m x y : B) (h : m ⊓ x = m ⊓ y) :
    inertOutsideValue m x = inertOutsideValue m y := by
  unfold inertOutsideValue
  rw [h]

def LocalTraceInclusion.patchMap {Q : ValuedPoset B N} {R : ValuedPoset B M} {m : B}
    (F : LocalTraceInclusion Q R m) (p : TotalCondition (inertOutside Q m)) :
    TotalCondition (inertOutside R m) :=
  ⟨p.mask,F.label p.trace,p.nonzero,by
    change p.mask ≤ inertOutsideValue m (R.valid (F.label p.trace))
    rw [inertOutside_eq_of_clip m _ _ (F.valid p.trace)]
    exact p.valid⟩

theorem LocalTraceInclusion.patchOrder_iff {Q : ValuedPoset B N}
    {R : ValuedPoset B M} {m : B} (F : LocalTraceInclusion Q R m)
    (p q : TotalCondition (inertOutside Q m)) :
    F.patchMap p ≤ F.patchMap q ↔ p ≤ q := by
  change (p.mask ≤ q.mask ∧ p.mask ≤ inertOutsideValue m (R.refines (F.label p.trace) (F.label q.trace))) ↔
    (p.mask ≤ q.mask ∧ p.mask ≤ inertOutsideValue m (Q.refines p.trace q.trace))
  rw [inertOutside_eq_of_clip m _ _ (F.refines p.trace q.trace)]

theorem LocalTraceInclusion.patch_reflect_compat {Q : ValuedPoset B N}
    {R : ValuedPoset B M} {m : B} (F : LocalTraceInclusion Q R m)
    {p q : TotalCondition (inertOutside Q m)} :
    Compatible (F.patchMap p) (F.patchMap q) → Compatible p q := by
  rw [totalCompatible_iff_r426,totalCompatible_iff_r426]
  simp only [inertOutside_common]
  have h : inertOutsideValue m (commonRefinementValue R (F.label p.trace) (F.label q.trace)) ≤
      inertOutsideValue m (commonRefinementValue Q p.trace q.trace) :=
    sup_le_sup_right (F.reflectCommon p.trace q.trace) _
  exact fun hn he => hn (le_bot_iff.mp
    ((inf_le_inf_left (p.mask ⊓ q.mask) h).trans_eq he))

def toPatchCondition (Q : ValuedPoset B N) (m : B) (p : MaskedCondition Q m) :
    TotalCondition (inertOutside Q m) :=
  ⟨p.val.mask,p.val.trace,p.val.nonzero,(le_inf p.property p.val.valid).trans le_sup_left⟩

private theorem le_raw_of_clip {m a x : B} (hm : a ≤ m)
    (h : a ≤ inertOutsideValue m x) : a ≤ x := by
  have h' := le_inf hm h
  rw [inertOutside_clip] at h'
  exact h'.trans inf_le_right

def fromPatchCondition (Q : ValuedPoset B N) (m : B)
    (p : TotalCondition (inertOutside Q m)) (hm : p.mask ≤ m) :
    MaskedCondition Q m :=
  ⟨⟨p.mask,p.trace,p.nonzero,le_raw_of_clip hm p.valid⟩,hm⟩

theorem toPatch_order_iff (Q : ValuedPoset B N) (m : B)
    (p q : MaskedCondition Q m) :
    toPatchCondition Q m p ≤ toPatchCondition Q m q ↔ p ≤ q := by
  constructor
  · exact fun h => ⟨h.1,le_raw_of_clip p.property h.2⟩
  · exact fun h => ⟨h.1,(le_inf p.property h.2).trans le_sup_left⟩

theorem toPatch_fromPatch (Q : ValuedPoset B N) (m : B)
    (p : TotalCondition (inertOutside Q m)) (h : p.mask ≤ m) :
    toPatchCondition Q m (fromPatchCondition Q m p h) = p := by
  cases p
  rfl

def LocalTraceInclusion.insideMap {Q : ValuedPoset B N}
    {R : ValuedPoset B M} {m : B} (F : LocalTraceInclusion Q R m)
    (p : MaskedCondition Q m) :
    MaskedCondition R m :=
  fromPatchCondition R m (F.patchMap (toPatchCondition Q m p)) p.property

theorem LocalTraceInclusion.inside_commutes {Q : ValuedPoset B N}
    {R : ValuedPoset B M} {m : B} (F : LocalTraceInclusion Q R m)
    (p : MaskedCondition Q m) :
    toPatchCondition R m (F.insideMap p) =
      F.patchMap (toPatchCondition Q m p) := toPatch_fromPatch _ _ _ _

end JSP000930.Negative
