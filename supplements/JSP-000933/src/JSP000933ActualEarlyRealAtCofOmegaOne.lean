import JSP000933CofOmegaOnePrefixSupport

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing BooleanCompletion CantorCodes OpenGraphForcing

variable {B N A : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra A]

theorem rankedInitialGreedy_preimage_r489 (Q : ValuedPoset B N)
    (F : CompleteValueMap A (TotalBA Q)) (base : B→A)
    (hBase : ∀ v,F.toFun (base v)=baseEmbed Q v)
    (E : MixedEnumeration OmegaOneIndex N B) (rank : N→OmegaOneIndex)
    (x : TotalBA Q) (c b : OmegaOneIndex)
    (hTrace : ∀ n : {n : N // rank n<b},∃ y : A,F.toFun y=traceValue Q n.val) :
    ∃ y : A,F.toFun y=rankedInitialGreedy Q E rank x c b := by
  classical
  choose t ht using hTrace
  refine ⟨⨆ i : ↥(Set.Iio c),⨆ n : {n : N // rank n<b},
    base (greedyTraceWeight Q E x i.val n.val)⊓t n,?_⟩
  simp only [rankedInitialGreedy,traceRectangle,F.map_iSup,F.map_inf,hBase,ht]

theorem earlyReal_at_cofOmegaOne_r489 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B)
    (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d)
    (scope : N→Finset GroundContinuumSuccIndex) (hScope : ∀ n a,a∈scope n → a<d)
    (A : GroundContinuumSuccIndex→Type) [∀ a,CompleteBooleanAlgebra (A a)]
    (F : ∀ a,CompleteValueMap (A a) (TotalBA Q)) (base : ∀ a,B→A a)
    (hBase : ∀ a v,(F a).toFun (base a v)=baseEmbed Q v)
    (hTrace : ∀ a n,(∀ k∈scope n,k<a) → ∃ y : A a,(F a).toFun y=traceValue Q n)
    (x : ℕ→TotalBA Q) (p : TotalBA Q) (hp : p≠⊥) :
    ∃ (a : GroundContinuumSuccIndex) (r : TotalCondition Q) (y : ℕ→A a),
      a<d ∧ imageCondition r≤p ∧ imageCondition r≤realEqValue x (fun j => (F a).toFun (y j)) := by
  classical
  obtain ⟨rank,c,b,a,m,r,ha,_,hr,hs,hEq⟩ :=
    localReal_of_cofOmegaOnePrefix_r488 Q hQ hB E d hd scope hScope x p hp
  have hY (j : ℕ) : ∃ y : A a,(F a).toFun y=rankedInitialGreedy Q E rank (x j) c b :=
    rankedInitialGreedy_preimage_r489 Q (F a) (base a) (hBase a) E rank (x j) c b
      (fun n => hTrace a n.val (hs n.val n.property))
  choose y hy using hY
  refine ⟨a,r,y,ha,hr.trans inf_le_left,(le_realEqValue_iff_r126 _ _ _).mpr ?_⟩
  intro j
  have h := congrArg (fun z => imageCondition r⊓z) (hEq j)
  have hR : imageCondition r⊓baseEmbed Q m=imageCondition r := inf_eq_left.mpr (hr.trans inf_le_right)
  rw [← inf_assoc,← inf_assoc,hR] at h
  exact h.trans (congrArg (fun z => imageCondition r⊓z) (hy j).symm)

end RelativeOCA
end JSP000933
