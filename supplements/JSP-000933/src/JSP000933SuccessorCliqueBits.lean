import JSP000933TypedStageMap

namespace JSP000933
namespace BooleanCompletion

theorem imageCondition_inf_le_of_common_r123 {P : Type} [Preorder P]
    (q r : P) (V : RO P) (h : ∀ s : P, s ≤ q → s ≤ r → imageCondition s ≤ V) :
    imageCondition q ⊓ imageCondition r ≤ V := by
  by_contra hNot
  let c := (imageCondition q ⊓ imageCondition r) ⊓ Vᶜ
  have hc : c ≠ ⊥ := by
    intro he
    apply hNot
    have hd : Disjoint (imageCondition q ⊓ imageCondition r) Vᶜ :=
      disjoint_iff_inf_le.mpr he.le
    exact (le_compl_iff_disjoint_right.mpr hd).trans_eq (compl_compl V)
  obtain ⟨s,hsq,hsr,hsc⟩ := FiniteSupport.exists_common_prefix_below_r86 q r hc
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  have hd := le_inf (h s hsq hsr) (hsc.trans inf_le_right)
  exact imageCondition_ne_bot_r50 s (le_bot_iff.mp (by simpa only [inf_compl_eq_bot] using hd))

end BooleanCompletion

namespace CantorCodes

open BooleanCompletion FiniteSupport

variable {A I : Type} [LinearOrder A] [WellFoundedLT A] [DecidableEq I]
variable (policy : StagePolicy A (ReverseLabels I)) {a b : A}

noncomputable def successorCliqueBit (a b : A) (i : I) : RO (Before (iterationRules policy) b) :=
  ⨆ q : {q : Before (iterationRules policy) b //
    ∃ s : ReverseLabels I, q.1.trace a = some s ∧ i ∈ OrderDual.ofDual s}, imageCondition q.1

variable {p : RO (GoodPrefix (earlierValidated policy a))}
variable {d : I → RO (GoodPrefix (earlierValidated policy a))}
variable {K : I → I → RO (GoodPrefix (earlierValidated policy a))}

variable (hVal : ∀ s : ReverseLabels I,
  policy a (earlierValidated policy a) s = cliqueAdmitted p d K (OrderDual.ofDual s))

include hVal

private theorem stage_value_of_present_r123 (hab : a ≤ b)
    (q : Before (iterationRules policy) b) (s : ReverseLabels I) (hs : q.1.trace a = some s) :
    imageCondition q ≤ (typedStageMap policy hab).toFun (cliqueAdmitted p d K (OrderDual.ofDual s)) := by
  have hBasic : imageCondition (typedRestrict policy q.1 a) ≤ cliqueAdmitted p d K (OrderDual.ofDual s) := by
    rw [← hVal s]
    exact (earlierStageValidity_iff_r85 policy q.1 a s).mp (q.1.valid a s hs)
  exact (image_le_typedStageMap_restrict_r122 policy hab q).trans
    ((typedStageMap policy hab).monotone hBasic)

theorem successorCliqueBit_le_vertex_r123 (hab : a ≤ b) (i : I) :
    successorCliqueBit policy a b i ≤ (typedStageMap policy hab).toFun (p ⊓ d i) := by
  apply iSup_le
  rintro ⟨q,s,hs,hi⟩
  exact (stage_value_of_present_r123 policy hVal hab q s hs).trans
    ((typedStageMap policy hab).monotone (cliqueAdmitted_le_vertex_r121 p d K hi))

theorem successorCliqueBit_pair_le_edge_r123 (hab : a ≤ b) {i j : I} (hne : i ≠ j) :
    successorCliqueBit policy a b i ⊓ successorCliqueBit policy a b j ≤
      (typedStageMap policy hab).toFun (K i j) := by
  unfold successorCliqueBit
  rw [iSup_inf_eq]
  apply iSup_le
  rintro ⟨q,s,hs,hi⟩
  rw [inf_iSup_eq]
  apply iSup_le
  rintro ⟨r,t,ht,hj⟩
  apply imageCondition_inf_le_of_common_r123 q r
  intro z hzq hzr
  obtain ⟨u,hu,hus⟩ := hzq a s hs
  obtain ⟨v,hv,hvt⟩ := hzr a t ht
  have huv : u = v := Option.some.inj (hu.symm.trans hv)
  have hI : i ∈ OrderDual.ofDual u := hus hi
  have hJ : j ∈ OrderDual.ofDual u := by
    rw [huv]
    exact hvt hj
  exact (stage_value_of_present_r123 policy hVal hab z u hu).trans
    ((typedStageMap policy hab).monotone (cliqueAdmitted_le_edge_r121 p d K hI hJ hne))

theorem successorCliqueBit_nonzero_r123
    (succ : ∀ i : A, i < b ↔ i ≤ a) (hp : p ≠ ⊥) (i : I) (hd : p ≤ d i) :
    successorCliqueBit policy a b i ≠ ⊥ := by
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 p hp
  let s : ReverseLabels I := OrderDual.toDual {i}
  have hs : imageCondition r ≤ policy a (earlierValidated policy a) s := by
    rw [hVal s,show OrderDual.ofDual s = {i} from rfl,cliqueAdmitted_singleton_r121]
    exact hr.trans (le_inf le_rfl hd)
  let q := attachCondition policy succ r s hs
  have hq : q.1.trace a = some s := by
    change attachTrace r.trace a s a = some s
    simp only [attachTrace,ite_true]
  have hle : imageCondition q ≤ successorCliqueBit policy a b i :=
    le_iSup_of_le ⟨q,s,hq,Finset.mem_singleton_self i⟩ le_rfl
  exact fun h => imageCondition_ne_bot_r50 q (le_bot_iff.mp (hle.trans_eq h))

end CantorCodes
end JSP000933
