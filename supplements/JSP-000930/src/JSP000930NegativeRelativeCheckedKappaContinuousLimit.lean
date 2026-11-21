import JSP000930NegativeCompleteStageTowerOccurrences
import JSP000933PreparedKappaBounds

open Cardinal

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion
  JSP000933.PreparedModel

variable {B D : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable {A : GroundContinuumSuccIndex → Type} [∀ a,CompleteBooleanAlgebra (A a)]

theorem projectedCCC_of_checkedKappa_tower
    (hB : BoundsCountableOmegaOneNames B) (hK : BoundsSmallKappaNames B)
    (F : CompleteValueMap B D) (T : CompleteStageTower F A)
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  intro x hx
  let m := unboundedValue (fun i => prefixReduce F (x i))
  let J := StageOccurrence T x
  let row := fun v : J => v.row
  let W := fun v : J => prefixReduce F ((T.stage v.stage).toFun v.value)
  obtain ⟨S⟩ := exists_segmentedOmegaChoices hB row row W m
    (stageOccurrence_tail_projects T x m le_rfl)
  let V (i : OmegaOneIndex) (a : GroundContinuumSuccIndex) :=
    ⨆ j : {j : J // j.stage ≤ a},(S.pick i).value j.val
  have hMono (i : OmegaOneIndex) : Monotone (V i) := by
    intro a b hab
    apply iSup_le
    intro j
    exact le_iSup (fun l : {j : J // j.stage ≤ b} => (S.pick i).value l.val)
      ⟨j.val,j.property.trans hab⟩
  have hV (i : OmegaOneIndex) : m ≤ ⨆ a,V i a := by
    rw [← (S.pick i).covers]
    apply iSup_le
    intro j
    exact le_iSup_of_le j.stage (le_iSup (fun k : {v : J // v.stage ≤ j.stage} =>
      (S.pick i).value k.val) ⟨j,le_rfl⟩)
  have hOmega : Cardinal.mk OmegaOneIndex < GroundContinuumSucc := by
    rw [mk_OmegaOneIndex_r61]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  have hAll := uniform_smallKappa_cutoffs_r473 hK hOmega m V hMono hV
  change m = ⊥
  apply le_bot_iff.mp
  apply (le_inf le_rfl hAll).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  let b := m ⊓ (⨅ i,V i a)
  let lift (v : {v : J // v.stage ≤ a}) : A a :=
    (T.shift v.val.stage a v.property).toFun v.val.value
  let Y (i : OmegaOneIndex) : A a :=
    ⨆ v : {v : J // v.stage ≤ a},lift v ⊓ (T.base a).toFun (b ⊓ (S.pick i).value v.val)
  have hProj (i : OmegaOneIndex) : prefixReduce (T.base a) (Y i) = b := by
    change prefixReduce (T.base a) (⨆ v : {v : J // v.stage ≤ a},
      lift v ⊓ (T.base a).toFun (b ⊓ (S.pick i).value v.val)) = b
    rw [(prefixReduce_gc (T.base a)).l_iSup]
    have hMap (v : {v : J // v.stage ≤ a}) :
        prefixReduce (T.base a) (lift v) = W v.val := by
      rw [← T.project_base a (lift v)]
      simp only [lift,W,T.shift_coherent]
    have he (v : {v : J // v.stage ≤ a}) :
        W v.val ⊓ (b ⊓ (S.pick i).value v.val) = b ⊓ (S.pick i).value v.val :=
      inf_eq_right.mpr (inf_le_right.trans (S.valid i v.val))
    simp only [prefixReduce_meet_of_embedded,hMap,he]
    rw [← inf_iSup_eq]
    exact inf_eq_left.mpr (inf_le_right.trans (iInf_le _ i))
  have hD (i j : OmegaOneIndex) (hij : i < j) : Disjoint (Y i) (Y j) := by
    apply disjoint_iff_inf_le.mpr
    apply (T.stage a).reflect_le_r93
    simp only [Y,(T.stage a).map_inf,(T.stage a).map_iSup,(T.stage a).map_bot,
      T.base_coherent,lift,T.shift_coherent,iSup_inf_iSup]
    apply iSup_le
    rintro ⟨v,w⟩
    by_cases hR : row v.val < row w.val
    · exact disjoint_iff_inf_le.mp ((hx _ _ hR).mono (inf_le_left.trans v.val.below)
        (inf_le_left.trans w.val.below))
    · have hZ : (S.pick i).value v.val ⊓ (S.pick j).value w.val = ⊥ := by
        apply le_bot_iff.mp
        rw [inf_comm]
        have hG := (inf_le_inf (S.separated i j hij w.val) le_rfl).trans
          (guardByChoice_elim_r445 (S.pick i) (fun t => occurrenceBefore row row t w.val) v.val)
        simpa only [occurrenceBefore,ite_eq_right hR] using hG
      have hZero : F.toFun ((S.pick i).value v.val) ⊓ F.toFun ((S.pick j).value w.val) = ⊥ := by
        rw [← F.map_inf,hZ,F.map_bot]
      apply le_bot_iff.mpr
      exact le_bot_iff.mp ((inf_le_inf
        (inf_le_right.trans (F.monotone inf_le_right))
        (inf_le_right.trans (F.monotone inf_le_right))).trans_eq hZero)
  have hStop := hCCC a Y hD
  rw [show (fun i => prefixReduce (T.base a) (Y i)) = fun _ => b from funext hProj,
    unboundedValue_const_r475] at hStop
  exact hStop.le

end JSP000930.Negative
