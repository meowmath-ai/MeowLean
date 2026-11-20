import JSP000933ActualNamedInputSnapshotBudget

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def GroundApproxEverySubset {j : ℕ} (D : ActualBlockSnapshot j) (k : ℕ) (W : Finset ℕ) : Prop :=
  ∀ z : Finset ℕ, z⊆W → ∃ a : BlockInput D.history, GroundAllBudgets true k (xorFinset z (D.act a∩W))

theorem xorFinset_slice_subset_r375 {z w W : Finset ℕ} (hz : z⊆W) :
    xorFinset z (w∩W)⊆W := by
  intro m hm
  rcases Finset.mem_union.mp hm with h | h
  · exact hz (Finset.mem_sdiff.mp h).1
  · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2

theorem xorFinset_slice_agrees_r375 (z w W : Finset ℕ) {m : ℕ} (hm : m∈W) :
    m∈xorFinset z (w∩W) ↔ m∈xorFinset z w := by
  simp only [xorFinset,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,hm,and_true]

theorem actualApproxEverySubset_eventually_r375 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (k : ℕ) (hk : k≠0) (W : ∀ j, ActualBlockSnapshot j → Finset ℕ) (hW : ∀ j D, W j D⊆D.range) :
    p≤eventuallyStageValue (fun j => snapshotPropValue T j (fun D => GroundApproxEverySubset D k (W j D))) := by
  classical
  let Far (j : ℕ) (D : ActualBlockSnapshot j) (z : Finset ℕ) :=
    z⊆W j D ∧ ∀ a : BlockInput D.history, ¬GroundAllBudgets true k (xorFinset z (D.act a∩W j D))
  let pick (j : ℕ) (D : ActualBlockSnapshot j) : Finset ℕ :=
    if h : ∃ z, Far j D z then Classical.choose h else ∅
  have hPickW (j : ℕ) (D : ActualBlockSnapshot j) : pick j D⊆W j D := by
    by_cases h : ∃ z, Far j D z
    · simpa only [pick,dite_eq_left h] using (Classical.choose_spec h).1
    · simp [pick,h]
  let y := actualSnapshotGluing T pick
  have hyS (j : ℕ) (D : ActualBlockSnapshot j) : pick j D⊆D.range := (hPickW j D).trans (hW j D)
  obtain ⟨x,hX,hXY⟩ := actualClampedOutput_onto_range_r365 F T hL y
    (actualSnapshotGluing_below_range_r369 T pick hyS)
  let Z := bitsSymmDiff y (actualClampedOutput T x)
  have hz : LocalLE true p Z (fun _ => ⊥) := actualXorNull_of_localEq_r374 hXY.symm_r236
  have ht : p≤⨆ N, budgetTail (nameBudgetValue true (realBitsName Z) (realBitsName (fun _ => ⊥))) k N :=
    hz.trans (nameOrder_positiveTails_r229 true _ _ k hk)
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨N,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq _ (hqp.trans ht)
  refine ⟨r,hr,hrq,le_iSup_of_le N ?_⟩
  apply le_iInf
  intro j
  apply le_of_dense_named_refinements_r219
  intro s hs hsr
  obtain ⟨D,t,ht,hts,hD⟩ := exists_nonzero_below_choice_r135 s hs (actualBlockSnapshotValue T j.val)
    ((hsr.trans (hrq.trans hqp)).trans (actualBlockSnapshots_cover_r366 T j.val))
  obtain ⟨a,v,hv,hvt,hA⟩ := exists_decided_blockInput_r374 D.history x t ht
  have hvD := hvt.trans hD
  let E := xorFinset (pick j.val D) (D.act a∩W j.val D)
  have hE : E⊆D.range := (xorFinset_slice_subset_r375 (hPickW j.val D)).trans (hW j.val D)
  have hBig (m : ℕ) (hm : m∈E) : v≤Z m := by
    have hmR : m∈D.range := hE hm
    have hmW : m∈W j.val D := xorFinset_slice_subset_r375 (hPickW j.val D) hm
    have hY := actualSnapshotGluing_mask_r369 T (rangeSnapshotCarrier T) pick hyS D hvD m hmR
    have hZ := snapshot_act_arbitrary_r368 hC hvD x a hA m (D.range_le hmR)
    have he := (mask_xor_congr_r257 hY hZ).trans
      (congrArg (fun z : B => v⊓z) (crispFinsetBits_xor_r371 (pick j.val D) (D.act a) m))
    have hMem := (xorFinset_slice_agrees_r375 _ _ _ hmW).mp hm
    have hTop : v⊓Z m=v := by
      simpa only [Z, y, bitsSymmDiff_at_r298, symmDiff, sdiff_eq, inf_comm, crispFinsetBits, crispTruth,
        ite_eq_left hMem, inf_top_eq] using he
    exact hTop.symm.le.trans inf_le_right
  have hSmall : GroundAllBudgets true k E :=
    groundAllBudgets_from_namedTail_r374 hv true k N Z E hBig
      (fun m hm => j.property.trans ((rangeSnapshotCarrier T).ge_index j.val D v hv hvD m (hE hm)))
      (hvt.trans (hts.trans (hsr.trans hR)))
  have hGood : GroundApproxEverySubset D k (W j.val D) := by
    intro z hz
    by_contra hn
    have hBad : ∃ z, Far j.val D z := ⟨z,hz,fun a h => hn ⟨a,h⟩⟩
    have he := (Classical.choose_spec hBad).2 a
    exact he (by simpa only [E,pick,dite_eq_left hBad] using hSmall)
  have hG : v≤crispTruth B (GroundApproxEverySubset D k (W j.val D)) := by simp [crispTruth,hGood]
  exact ⟨v,hv,hvt.trans hts,le_iSup_of_le D (le_inf hvD hG)⟩

end SetLanguage
end JSP000933
