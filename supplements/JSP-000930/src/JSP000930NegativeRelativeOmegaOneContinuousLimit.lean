import JSP000930NegativeCheckedOmegaTowerReductions

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.CantorCodes

variable {B D : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable {A : OmegaOneIndex → Type} [∀ i,CompleteBooleanAlgebra (A i)]

noncomputable def regressiveReductionWeight {F : CompleteValueMap B D}
    (T : CheckedOmegaTower F A) (x : OmegaOneIndex → D) (d a : OmegaOneIndex) : B :=
  ⨆ q : TowerReduction T x d a,prefixReduce (T.base a) q.small

theorem regressiveReductionRows_cover {F : CompleteValueMap B D}
    (T : CheckedOmegaTower F A) (x : OmegaOneIndex → D) (m : B)
    (hM : m ≤ unboundedValue (fun i => prefixReduce F (x i)))
    (d : OmegaOneIndex) (hd : CheckedOmegaOneLimit d) :
    m ≤ ⨆ a : {a : OmegaOneIndex // a < d},regressiveReductionWeight T x d a.val := by
  let C := ⨆ a : {a : OmegaOneIndex // a < d},regressiveReductionWeight T x d a.val
  change m ≤ C
  by_contra hn
  let p := m ⊓ Cᶜ
  have hp : p ≠ ⊥ := fun he => hn
    (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  have hAbove : p ≤ ⨆ i : {i : OmegaOneIndex // d < i},prefixReduce F (x i.val) :=
    inf_le_left.trans (hM.trans (iInf_le _ d))
  obtain ⟨i,b,hb,hbp,hbx⟩ := exists_nonzero_below_choice_r135 p hp
    (fun i : {i : OmegaOneIndex // d < i} => prefixReduce F (x i.val)) hAbove
  have hX := prefixReduce_meet_ne_bot F hb hbx
  obtain ⟨s,y,hy,hyx⟩ := T.final_dense (x i.val ⊓ F.toFun b) hX
  let z := (T.stage s).toFun y
  have hz : prefixReduce (T.stage d) z ≠ ⊥ := prefixReduce_nonzero (T.stage d) hy
  obtain ⟨a,ha,q,hq,hqRed⟩ := T.limit_dense d hd (prefixReduce (T.stage d) z) hz
  let t : TowerReduction T x d a :=
    ⟨ha,i.val,i.property,s,y,q,hyx.trans inf_le_left,hqRed⟩
  have hZ : z ≤ (T.stage d).toFun ((T.base d).toFun b) := by
    rw [T.base_coherent]
    exact hyx.trans inf_le_right
  have hQ : (T.stage a).toFun q ≤ F.toFun b := by
    rw [← T.shift_coherent a d ha.le q,← T.base_coherent d]
    exact (T.stage d).monotone (hqRed.trans ((prefixReduce_le_iff (T.stage d) z _).2 hZ))
  let w := prefixReduce (T.base a) q
  have hw : w ≠ ⊥ := prefixReduce_nonzero (T.base a) hq
  have hwb : w ≤ b := by
    change prefixReduce (T.base a) q ≤ b
    rw [← checkedTower_project_base F T a q]
    exact (prefixReduce_le_iff F _ _).2 hQ
  have hWC : w ≤ C := le_iSup_of_le ⟨a,ha⟩
    (le_iSup (fun j : TowerReduction T x d a => prefixReduce (T.base a) j.small) t)
  exact hw (disjoint_compl_right.out _ hWC (hwb.trans (hbp.trans inf_le_right)))

variable {P : Type} [Preorder P]

theorem projectedCCC_of_checkedOmegaOne_tower
    (hP : IsCountablyClosed P) (hB : BoundsCountableOmegaOneNames (RO P))
    (F : CompleteValueMap (RO P) D) (T : CheckedOmegaTower F A)
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  intro x hx
  let m := unboundedValue (fun i => prefixReduce F (x i))
  change m = ⊥
  have hReg : m ≤ ⨆ a,unboundedValue (fun j => regressiveReductionWeight T x j a) :=
    relative_regressive_limit_rows_unbounded hP m (regressiveReductionWeight T x)
      (regressiveReductionRows_cover T x m le_rfl)
  apply le_bot_iff.mp
  apply hReg.trans
  apply iSup_le
  intro a
  let J := Σ d : OmegaOneIndex,TowerReduction T x d a
  let row (j : J) := j.1
  let rank (j : J) := max j.1 (max j.2.sourceStage j.2.row)
  let X (j : J) := j.2.small
  let W (j : J) := prefixReduce (T.base a) (X j)
  let u := unboundedValue (fun j => regressiveReductionWeight T x j a)
  have hW : ∀ b,u ≤ ⨆ j : {j : J // b < row j},W j.val := by
    intro b
    apply (iInf_le _ b).trans
    apply iSup_le
    intro i
    apply iSup_le
    intro q
    exact le_iSup (fun j : {j : J // b < row j} => W j.val) ⟨⟨i.val,q⟩,i.property⟩
  have hSep (i j : J) (h : rank i < row j) : Disjoint (X i) (X j) := by
    exact i.2.apart_when_late hx j.2
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt h))
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt h))
  exact (projectedCCC_forbids_skew_unbounded hB (T.base a) (hCCC a) rank row X W
    (fun _ => le_rfl) hSep u hW).le

end JSP000930.Negative
