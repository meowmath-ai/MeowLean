import JSP000930NegativeRelativeOmegaOneContinuousLimit

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.CantorCodes

variable {B D I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable [LinearOrder I] {A : I → Type} [∀ a,CompleteBooleanAlgebra (A a)]

structure CompleteStageTower (F : CompleteValueMap B D)
    (A : I → Type) [∀ i,CompleteBooleanAlgebra (A i)] where
  stage : ∀ i,CompleteValueMap (A i) D
  base : ∀ i,CompleteValueMap B (A i)
  shift : ∀ i j,i ≤ j → CompleteValueMap (A i) (A j)
  base_coherent : ∀ i b,(stage i).toFun ((base i).toFun b) = F.toFun b
  shift_coherent : ∀ i j (h : i ≤ j) a,
    (stage j).toFun ((shift i j h).toFun a) = (stage i).toFun a
  final_dense : ∀ x : D,x ≠ ⊥ → ∃ (i : I) (a : A i),
    (stage i).toFun a ≠ ⊥ ∧ (stage i).toFun a ≤ x

theorem CompleteStageTower.project_base {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) (i : I) (a : A i) :
    prefixReduce F ((T.stage i).toFun a) = prefixReduce (T.base i) a := by
  have eq (b : B) : prefixReduce F ((T.stage i).toFun a) ≤ b ↔
      prefixReduce (T.base i) a ≤ b := by
    rw [prefixReduce_le_iff,prefixReduce_le_iff,← T.base_coherent i]
    exact ⟨(T.stage i).reflect_le_r93, fun h => (T.stage i).monotone h⟩
  exact le_antisymm ((eq _).2 le_rfl) ((eq _).1 le_rfl)

structure StageOccurrence {F : CompleteValueMap B D} (T : CompleteStageTower F A)
    (X : OmegaOneIndex → D) where
  row : OmegaOneIndex
  stage : I
  value : A stage
  below : (T.stage stage).toFun value ≤ X row

theorem stageOccurrence_tail_projects {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) (X : OmegaOneIndex → D)
    (m : B) (hm : m ≤ unboundedValue (fun i => prefixReduce F (X i)))
    (b : OmegaOneIndex) :
    m ≤ ⨆ v : {v : StageOccurrence T X // b < v.row},
      prefixReduce F ((T.stage v.val.stage).toFun v.val.value) := by
  let U := ⨆ v : {v : StageOccurrence T X // b < v.row},
    prefixReduce F ((T.stage v.val.stage).toFun v.val.value)
  change m ≤ U
  by_contra hn
  let p := m ⊓ Uᶜ
  have hp : p ≠ ⊥ := fun he => hn
    (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  have hAbove : p ≤ ⨆ i : {i : OmegaOneIndex // b < i},prefixReduce F (X i.val) :=
    inf_le_left.trans (hm.trans (iInf_le _ b))
  obtain ⟨i,s,hs,hsp,hSX⟩ := exists_nonzero_below_choice_r135 p hp
    (fun i : {i : OmegaOneIndex // b < i} => prefixReduce F (X i.val)) hAbove
  have hX := prefixReduce_meet_ne_bot F hs hSX
  obtain ⟨a,y,hy,hyX⟩ := T.final_dense _ hX
  let v : StageOccurrence T X := ⟨i.val,a,y,hyX.trans inf_le_left⟩
  let g := prefixReduce F ((T.stage a).toFun y)
  have hg : g ≠ ⊥ := prefixReduce_nonzero F hy
  have hgs : g ≤ s := (prefixReduce_le_iff F _ _).2 (hyX.trans inf_le_right)
  have hgU : g ≤ U := le_iSup (fun t : {t : StageOccurrence T X // b < t.row} =>
    prefixReduce F ((T.stage t.val.stage).toFun t.val.value)) ⟨v,i.property⟩
  exact hg (disjoint_compl_right.out _ hgU (hgs.trans (hsp.trans inf_le_right)))

end JSP000930.Negative
