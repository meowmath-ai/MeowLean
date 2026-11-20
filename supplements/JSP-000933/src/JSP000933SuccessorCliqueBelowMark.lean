import JSP000933SuccessorCliqueBits

namespace JSP000933
namespace CantorCodes

open BooleanCompletion FiniteSupport OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem countableCoverage_above_compl_r124 (g : I → B) (p : B) (hg : ∀ i, g i ≤ p) :
    pᶜ ≤ countableCoverageValue g := by
  let e : EnumerationMatrix I B := ⟨fun _ _ => ⊥,fun _ _ _ _ => disjoint_bot_left⟩
  unfold countableCoverageValue
  apply le_iSup_of_le e
  apply le_iInf
  intro i
  exact (compl_le_compl (hg i)).trans le_sup_left

variable {A : Type} [LinearOrder A] [WellFoundedLT A] [DecidableEq I]
variable (policy : StagePolicy A (ReverseLabels I)) {a b : A}
variable {p : RO (GoodPrefix (earlierValidated policy a))}
variable {d : I → RO (GoodPrefix (earlierValidated policy a))}
variable {K : I → I → RO (GoodPrefix (earlierValidated policy a))}

theorem exists_successorClique_below_mark_r124
    (succ : ∀ i : A, i < b ↔ i ≤ a)
    (hVal : ∀ s : ReverseLabels I,
      policy a (earlierValidated policy a) s = cliqueAdmitted p d K (OrderDual.ofDual s))
    (hCCC : HasCountableAntichains (Before (iterationRules policy) b))
    (hI : ¬ Countable I) (hp : p ≠ ⊥) (hd : ∀ i, p ≤ d i) :
    let hab := ((succ a).mpr le_rfl).le
    let F := typedStageMap policy hab
    let g := successorCliqueBit policy a b
    ∃ q : Before (iterationRules policy) b,
      imageCondition q ≤ F.toFun p ∧
      imageCondition q ≤ (countableCoverageValue g)ᶜ ∧
      (∀ i, g i ≤ F.toFun (d i)) ∧
      (∀ i j, i ≠ j → g i ⊓ g j ≤ F.toFun (K i j)) := by
  intro hab F g
  have hG (i : I) : g i ≤ F.toFun (p ⊓ d i) :=
    successorCliqueBit_le_vertex_r123 policy hVal hab i
  have hpG (i : I) : g i ≤ F.toFun p := (hG i).trans (F.monotone inf_le_left)
  have hc := countableCoverage_above_compl_r124 g (F.toFun p) hpG
  have hN : countableCoverageValue g ≠ ⊤ :=
    countableCoverageValue_ne_top_r68 (booleanCCC_of_conditionCCC_r66 hCCC) hI g
      (fun i => successorCliqueBit_nonzero_r123 policy hVal succ hp i (hd i))
  have hn : (countableCoverageValue g)ᶜ ≠ ⊥ := by
    intro h
    apply hN
    apply compl_injective
    simpa only [compl_top] using h
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 (countableCoverageValue g)ᶜ hn
  have hqp : imageCondition q ≤ F.toFun p :=
    (hq.trans (compl_le_compl hc)).trans_eq (compl_compl _)
  exact ⟨q,hqp,hq,fun i => (hG i).trans (F.monotone inf_le_right),
    fun _ _ hne => successorCliqueBit_pair_le_edge_r123 policy hVal hab hne⟩

end CantorCodes
end JSP000933
