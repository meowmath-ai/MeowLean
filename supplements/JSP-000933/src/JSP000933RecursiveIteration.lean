import JSP000933StaticPrefix

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {A T : Type} [LinearOrder A] [WellFoundedLT A] [Preorder T]

abbrev StagePolicy (A T : Type) [LinearOrder A] [Preorder T] :=
  (a : A) → (old : PrefixValidator a T) → T → RO (GoodPrefix old)

noncomputable def localStageValid (policy : StagePolicy A T) : (a : A) → LabelTrace A T → T → Prop :=
  WellFounded.fix wellFounded_lt (fun a old p t => rawProjection old p ≤ policy a old t)

theorem localStageValid_unfold_r85 (policy : StagePolicy A T) (a : A) (p : LabelTrace A T) (t : T) :
    localStageValid policy a p t ↔
      rawProjection (fun j (_ : j < a) => localStageValid policy j) p ≤
        policy a (fun j (_ : j < a) => localStageValid policy j) t := by
  have h := WellFounded.fix_eq wellFounded_lt
    (fun a (old : PrefixValidator a T) p t => rawProjection old p ≤ policy a old t) a
  exact Iff.of_eq (congrFun (congrFun h p) t)

noncomputable def iterationRules (policy : StagePolicy A T) : Rules (fun (_ : A) => T) where
  valid := localStageValid policy
  leAt := fun _ _ q r => q ≤ r
  refl := fun _ _ _ => le_rfl
  trans := fun _ _ _ _ _ hp hq => hp.trans hq
  persist_valid := by
    intro i p q t h hq
    apply (localStageValid_unfold_r85 policy i (cut p i) t).mpr
    exact (rawProjection_mono_r84 (fun j (_ : j < i) => localStageValid policy j)
      (rawStronger_cut_r84 i h)).trans ((localStageValid_unfold_r85 policy i (cut q i) t).mp hq)
  persist_le := fun _ _ _ _ _ _ h => h

abbrev IterationCondition (policy : StagePolicy A T) :=
  Condition (iterationRules policy)

def earlierValidated (policy : StagePolicy A T) (a : A) : PrefixValidator a T :=
  fun j _ => localStageValid policy j

noncomputable def prefixOrderIso_r85 (policy : StagePolicy A T) (a : A) :
    Before (iterationRules policy) a ≃o GoodPrefix (earlierValidated policy a) where
  toFun p := ⟨p.1.trace,p.1.finite,p.2,fun i _ s hs => p.1.valid i s hs⟩
  invFun q := ⟨⟨q.trace,q.finite,fun i s hs => q.valid i (q.bounded i ⟨s,hs⟩) s hs⟩,q.bounded⟩
  left_inv := by
    rintro ⟨⟨p,hF,hV⟩,hB⟩
    rfl
  right_inv := by
    rintro ⟨p,hF,hB,hV⟩
    rfl
  map_rel_iff' := Iff.rfl

noncomputable def typedRestrict (policy : StagePolicy A T) (p : IterationCondition policy) (a : A) :
    GoodPrefix (earlierValidated policy a) :=
  prefixOrderIso_r85 policy a (restrict p a)

theorem earlierStageValidity_iff_r85 (policy : StagePolicy A T)
    (p : IterationCondition policy) (a : A) (s : T) :
    localStageValid policy a (cut p.trace a) s ↔
      imageCondition (typedRestrict policy p a) ≤ policy a (earlierValidated policy a) s := by
  refine (localStageValid_unfold_r85 policy a (cut p.trace a) s).trans ?_
  exact Iff.of_eq (congrArg (fun b => b ≤ policy a (earlierValidated policy a) s)
    (rawProjection_of_good_r84 (earlierValidated policy a) (typedRestrict policy p a)))

end FiniteSupport
end JSP000933
