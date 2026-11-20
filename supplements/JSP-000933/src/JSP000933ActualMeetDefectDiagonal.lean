import JSP000933ActualNullWindowBudgets

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def blockInputMeet {k : ℕ} {H : ActualStageHistory (k+2)} (x y : BlockInput H) : BlockInput H :=
  ⟨x.val∩y.val,Finset.mem_powerset.mpr ((Finset.inter_subset_left).trans (Finset.mem_powerset.mp x.property))⟩

def snapshotActMeetDefect {k : ℕ} (D : ActualBlockSnapshot k) (x y : BlockInput D.history) : Finset ℕ :=
  xorFinset (D.act x∩D.act y) (D.act (blockInputMeet x y))

theorem snapshotActMeetDefect_subset_r371 {k : ℕ} (D : ActualBlockSnapshot k) (x y : BlockInput D.history) :
    snapshotActMeetDefect D x y⊆D.range := by
  intro m hm
  rcases Finset.mem_union.mp hm with h | h
  · exact D.act_le x (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1
  · exact D.act_le _ (Finset.mem_sdiff.mp h).1

theorem crispFinsetBits_inter_r371 (x y : Finset ℕ) (m : ℕ) :
    crispFinsetBits (B := B) x m⊓crispFinsetBits y m=crispFinsetBits (x∩y) m := by
  unfold crispFinsetBits
  rw [← crisp_and_r190]
  exact crispTruth_propext_r188 (Finset.mem_inter.symm)

theorem crispFinsetBits_xor_r371 (x y : Finset ℕ) (m : ℕ) :
    bitsSymmDiff (crispFinsetBits (B := B) x) (crispFinsetBits y) m=crispFinsetBits (xorFinset x y) m := by
  unfold crispFinsetBits
  have he := crispXorSet_r340 (B := B) (x : Set ℕ) (y : Set ℕ) m
  have hw : (m∈xorSet (x : Set ℕ) (y : Set ℕ)) ↔ m∈xorFinset x y := by
    simp only [xorFinset,xorSet,Finset.mem_union,Finset.mem_sdiff,Set.mem_union,Set.mem_sdiff,Finset.mem_coe]
  exact he.trans (crispTruth_propext_r188 hw)

theorem actualMeetDefect_null_r371 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (x y : ℕ → B) (hx : p≤bitsBelowValue x (actualSourceUnion T))
    (hy : p≤bitsBelowValue y (actualSourceUnion T)) :
    LocalLE true p
      (bitsSymmDiff (bitsMeet (actualClampedOutput T x) (actualClampedOutput T y))
        (actualClampedOutput T (bitsMeet x y))) (fun _ => ⊥) := by
  let I := F.restrict_r246 (show p≤p from le_rfl)
  have hX := actualClampedOutput_harmEq_r364 F T hL x hx
  have hY := actualClampedOutput_harmEq_r364 F T hL y hy
  have hXY : p≤bitsBelowValue (bitsMeet x y) (actualSourceUnion T) :=
    bitsBelowValue_trans_r324 (bitsBelowValue_of_pointwise_r272 (fun _ => inf_le_left)) hx
  have hB := actualClampedOutput_harmEq_r364 F T hL (bitsMeet x y) hXY
  have hA := (hX.meet_congr_r239 hY).trans_r236 (I.mapMeet_r237 x y).symm_r236
  have he := hA.xor_congr_r346 hB
  have hZ : bitsSymmDiff (F.toName (bitsMeet x y)) (F.toName (bitsMeet x y))=(fun _ => ⊥) := by
    funext m
    rw [bitsSymmDiff_at_r298,symmDiff_self]
  change LocalEq true p _ (bitsSymmDiff (F.toName (bitsMeet x y)) (F.toName (bitsMeet x y))) at he
  rw [hZ] at he
  exact he.1

theorem actualChosenMeetDefect_eventuallyBudget_r371 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (k : ℕ) (hk : k≠0) (X Y : ∀ j (D : ActualBlockSnapshot j), BlockInput D.history) :
    p≤eventuallyStageValue (fun j => snapshotPieceGoodValue T true k j
      (fun D => snapshotActMeetDefect D (X j D) (Y j D))) := by
  let x := actualSnapshotGluing T (fun j D => (X j D).val)
  let y := actualSnapshotGluing T (fun j D => (Y j D).val)
  have hxS (j : ℕ) (D : ActualBlockSnapshot j) : (X j D).val⊆blockSnapshotSource D.history :=
    Finset.mem_powerset.mp (X j D).property
  have hyS (j : ℕ) (D : ActualBlockSnapshot j) : (Y j D).val⊆blockSnapshotSource D.history :=
    Finset.mem_powerset.mp (Y j D).property
  have hx := actualSnapshotGluing_below_source_r369 T _ hxS
  have hy := actualSnapshotGluing_below_source_r369 T _ hyS
  apply namedNull_containedSnapshot_eventuallyBudget_r370 T (rangeSnapshotCarrier T) true k hk _
    (actualMeetDefect_null_r371 F T hL x y hx hy) _ (fun j D => snapshotActMeetDefect_subset_r371 D _ _)
  intro j D m hm
  let q := actualBlockSnapshotValue T j D
  let S := blockSnapshotSource D.history
  let a := X j D
  let b := Y j D
  have hM : m∈groundStageWindow D.history j := D.range_le (snapshotActMeetDefect_subset_r371 D a b hm)
  have hX (i : ℕ) (hi : i∈S) : q⊓x i=q⊓crispFinsetBits a.val i :=
    actualSnapshotGluing_mask_r369 T (sourceSnapshotCarrier T) _ hxS D le_rfl i hi
  have hY (i : ℕ) (hi : i∈S) : q⊓y i=q⊓crispFinsetBits b.val i :=
    actualSnapshotGluing_mask_r369 T (sourceSnapshotCarrier T) _ hyS D le_rfl i hi
  have hXY (i : ℕ) (hi : i∈S) : q⊓bitsMeet x y i=q⊓crispFinsetBits (blockInputMeet a b).val i :=
    (mask_inf_congr_r126 (hX i hi) (hY i hi)).trans
      (congrArg (fun d : B => q⊓d) (crispFinsetBits_inter_r371 a.val b.val i))
  have hAX := snapshot_act_arbitrary_r368 hC (q := q) le_rfl x a hX m hM
  have hAY := snapshot_act_arbitrary_r368 hC (q := q) le_rfl y b hY m hM
  have hB := snapshot_act_arbitrary_r368 hC (q := q) le_rfl (bitsMeet x y) (blockInputMeet a b) hXY m hM
  have hA := (mask_inf_congr_r126 hAX hAY).trans
    (congrArg (fun d : B => q⊓d) (crispFinsetBits_inter_r371 (D.act a) (D.act b) m))
  have hE := (mask_xor_congr_r257 hA hB).trans
    (congrArg (fun d : B => q⊓d) (crispFinsetBits_xor_r371 (D.act a∩D.act b) (D.act (blockInputMeet a b)) m))
  have hTop : crispFinsetBits (B := B) (snapshotActMeetDefect D a b) m=⊤ := by
    have hm' : m ∈ snapshotActMeetDefect D a b := hm
    rw [crispFinsetBits,crispTruth,ite_eq_left hm']
  have he := hE.trans (congrArg (fun d : B => q⊓d) hTop)
  rw [inf_top_eq] at he
  exact he.symm.le.trans inf_le_right

end SetLanguage
end JSP000933
