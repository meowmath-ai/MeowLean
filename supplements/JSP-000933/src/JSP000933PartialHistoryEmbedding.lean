import JSP000933PartialHistory

namespace JSP000933
namespace BooleanCompletion

variable {P Q S : Type} [Preorder P] [Preorder Q] [Preorder S]

def RestrictionMap.comp (G : RestrictionMap Q S) (F : RestrictionMap P Q) :
    RestrictionMap P S where
  toFun := G.toFun ∘ F.toFun
  monotone := G.monotone.comp F.monotone
  onto := G.onto.comp F.onto
  lift := by
    intro p s hs
    obtain ⟨q,hq,hqs⟩ := G.lift (F.toFun p) s hs
    obtain ⟨r,hr,hrq⟩ := F.lift p q hq
    exact ⟨r,hr,(G.monotone hrq).trans hqs⟩

theorem RestrictionMap.comp_boolPullback_r132 (G : RestrictionMap Q S) (F : RestrictionMap P Q)
    (U : RO S) : (G.comp F).boolPullback U = F.boolPullback (G.boolPullback U) := by
  apply Heyting.Regular.coe_injective
  ext p
  rfl

end BooleanCompletion

namespace FiniteSupport

open BooleanCompletion

variable {A T : Type} [LinearOrder A] [Preorder T]

instance goodPrefixNonempty {a : A} (old : PrefixValidator a T) : Nonempty (GoodPrefix old) :=
  ⟨{
    trace := fun _ => none
    finite := by simp [present]
    bounded := fun _ ⟨s,h⟩ => by cases h
    valid := fun _ _ _ h => by cases h }⟩

def historyRestriction {a b : A} (hab : b ≤ a)
    (old : PrefixValidator a T) (hp : HistoryPersistent old) :
    RestrictionMap (GoodPrefix old) (GoodPrefix (subHistory hab old)) :=
  let e := partialHistoryPrefixIso_r131 (le_rfl : a ≤ a) old hp
  let f := partialHistoryPrefixIso_r131 hab old hp
  (orderIsoReduction f).comp ((prefixReduction (R := partialHistoryRules old hp) hab).comp
    (orderIsoReduction e.symm))

theorem historyRestriction_trace_r132 {a b : A} (hab : b ≤ a)
    (old : PrefixValidator a T) (hp : HistoryPersistent old) (p : GoodPrefix old) :
    ((historyRestriction hab old hp).toFun p).trace = cut p.trace b :=
  rfl

end FiniteSupport
end JSP000933
