import JSP000933GroundKappaTraceEnum

open Cardinal

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing PreparedModel CantorCodes

variable {B N I A : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra A]

theorem initialKappaGreedyValue_ground_r478 (Q : ValuedPoset B N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (x : TotalBA Q) (c : GroundContinuumSuccIndex) :
    initialKappaGreedyValue Q (groundMixedEnumeration f hf) x c=
      ⨆ i : ↥(Set.Iio c),traceRectangle Q (f i.val)
        (greedyTraceWeight Q (groundMixedEnumeration f hf) x i.val (f i.val)) := by
  classical
  let E : MixedEnumeration GroundContinuumSuccIndex N B := groundMixedEnumeration f hf
  unfold initialKappaGreedyValue
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro n
    by_cases h : f i.val=n
    · subst n
      exact le_iSup (fun j : ↥(Set.Iio c) => traceRectangle Q (f j.val)
        (greedyTraceWeight Q (groundMixedEnumeration f hf) x j.val (f j.val))) i
    · have z := greedyTraceWeight_cell_r465 Q (groundMixedEnumeration f hf) x i.val n
      have hCell : (groundMixedEnumeration (B := B) f hf).cell i.val n=⊥ := by
        simp only [groundMixedEnumeration,ite_eq_right h]
      rw [hCell] at z
      rw [le_bot_iff.mp z,traceRectangle_zero_r464]
      exact bot_le
  · apply iSup_le
    intro i
    exact le_iSup_of_le i (le_iSup (fun n : N => traceRectangle Q n
      (greedyTraceWeight Q E x i.val n)) (f i.val))

theorem earlierValue_of_rectangles_r478 (Q : ValuedPoset B N)
    (F : CompleteValueMap A (TotalBA Q)) (base : B→A)
    (hBase : ∀ b,F.toFun (base b)=baseEmbed Q b)
    (trace : I→N) (weight : I→B)
    (hTrace : ∀ i,∃ v : A,F.toFun v=traceValue Q (trace i)) :
    ∃ v : A,F.toFun v=⨆ i,traceRectangle Q (trace i) (weight i) := by
  classical
  choose t ht using hTrace
  refine ⟨⨆ i,base (weight i)⊓t i,?_⟩
  simp only [F.map_iSup,F.map_inf,hBase,ht,traceRectangle]

theorem locally_boundedGroundTraceNames_r478 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsSmallKappaNames B)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (stages : N→Finset GroundContinuumSuccIndex)
    (x : I→TotalBA Q) (hI : Cardinal.mk I<GroundContinuumSucc)
    (m : B) (hM : m≠⊥) :
    ∃ (c a : GroundContinuumSuccIndex) (b : B),b≠⊥ ∧ b≤ m ∧
      (∀ j<c,∀ k∈stages (f j),k<a) ∧
      ∀ i,baseEmbed Q b⊓x i=baseEmbed Q b⊓(
        ⨆ j : ↥(Set.Iio c),traceRectangle Q (f j.val)
            (greedyTraceWeight Q (groundMixedEnumeration f hf) (x i) j.val (f j.val))) := by
  let E : MixedEnumeration GroundContinuumSuccIndex N B := groundMixedEnumeration f hf
  let W := actualKappaCut_boundedFamilies Q E x
  have hTop : (⨆ c,W c)=⊤ := actualKappaCuts_cover_r476 Q hQ hB E x hI
  have hCov : m≤⨆ c,W c := hTop.symm ▸ le_top
  obtain ⟨c,b,hb,hbm,hbC⟩ := exists_nonzero_below_choice_r135 m hM W hCov
  obtain ⟨a,ha⟩ := groundKappaEnumeration_prefixStages_bounded_r477 f stages c
  refine ⟨c,a,b,hb,hbm,ha,fun i => ?_⟩
  exact (actualKappaCut_agrees_r476 Q E x c b hbC i).trans
    (congrArg (fun y => baseEmbed Q b⊓y) (initialKappaGreedyValue_ground_r478 Q f hf (x i) c))

end RelativeOCA
end JSP000933
