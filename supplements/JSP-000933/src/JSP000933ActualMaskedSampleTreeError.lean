import JSP000933OccupiedParitySampleGeometry

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actual_masked_sampleTree_small_r273
    {G : bSet B} {ks : ℕ → ℕ} {p q : B} (T : ActualBranchCrossingData G ks p)
    (j l : ℕ) (side : Bool) (b H Y z : ℕ → B) (hq : q≤p)
    (hDom : q≤namedBranchCrossDomain G (interleaveCrossQuad (actualParityCap T.freshCap j side) b H Y))
    (hCl : q≤ClosedMember (T.cover j) l (interleaveCrossQuad (actualParityCap T.freshCap j side) b H Y))
    (hTree : q≤fixedActualSampleTree T j l side
      (interleaveCrossQuad (actualParityCap T.freshCap j side) b H z)) :
    q ≤ smallAllPrefixes true (ks j) (bitsSymmDiff (bitsMeet H z) (bitsMeet H Y)) := by
  let a := actualParityCap T.freshCap j side
  let x := interleaveCrossQuad a b H Y
  let c := interleaveCrossQuad a b H z
  let E := bitsSymmDiff (bitsMeet H z) (bitsMeet H Y)
  change q ≤ smallAllPrefixes true (ks j) E
  unfold smallAllPrefixes
  apply le_iInf
  intro n
  let k := 2*max n l+colorParity (!side)
  have hk : max n l≤k := by dsimp [k]; omega
  have hl : l≤k := (le_max_right _ _).trans hk
  have hn : n≤actualSampleCut j k :=
    ((le_max_left _ _).trans hk).trans (self_le_actualSampleCut_r267 j k)
  have hParity : k%2≠colorParity side := by cases side <;> simp [k,colorParity] <;> omega
  have hU := fixedActualSampleTree_apply_r271 T j l side c hTree k hl hParity
  apply le_of_dense_named_refinements_r219
  intro r hr hrq
  obtain ⟨u,t,ht,htr,hT⟩ := exists_nonzero_below_choice_r135 r hr
    (fun u : {u : Word // u.length=4*actualSampleCut j k} =>
      closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u.val ⊓
        cylinderValue c u.val) (hrq.trans hU)
  let y := (T.samples j).nameFor l u.val
  have htq := htr.trans hrq
  have htp := htq.trans hq
  have hOcc := hT.trans inf_le_left
  have hQual := T.slotSample_qualifies_r272 j l u.val htp hOcc
  have hYD : t≤namedBranchCrossDomain G y := hQual.trans inf_le_left
  have hYC : t≤ClosedMember (T.cover j) l y := hQual.trans (inf_le_right.trans inf_le_left)
  have hCyl := hQual.trans (inf_le_right.trans inf_le_right)
  have hPre (m : ℕ) (hm : m<4*actualSampleCut j k) : t⊓c m=t⊓y m :=
    sameCylinder_mask_r261 (hT.trans inf_le_right) hCyl m (u.property.symm ▸ hm)
  have hXBelow : t≤bitsBelowValue (crossPay c) (crossCap c) := by
    simpa only [c,x,crossPay_interleaveCrossQuad_r271,crossCap_interleaveCrossQuad_r271] using
      (htq.trans (hDom.trans (concreteCrossDomain_below_r260 neatBranchLabeling G branchCapExtra x)))
  have hYBelow := hYD.trans (concreteCrossDomain_below_r260 neatBranchLabeling G branchCapExtra y)
  have hAfter : t≤afterCutDisjointValue (crossCap y) (crossCap c) (actualSampleCut j k) := by
    simpa only [c,a,crossCap_interleaveCrossQuad_r271] using
      (T.occupiedParitySample_beforePrefix_r272 j l k side u.val hl hParity u.property htp hOcc)
  have hSrcC := sourceCrossEq_of_prefix_and_late_disjoint_r270 c y (actualSampleCut j k) hPre hAfter hXBelow hYBelow
  have hSrcX : t ≤ sourceCrossEq x y := by
    simpa only [sourceCrossEq,c,x,crossPay_interleaveCrossQuad_r271,crossCap_interleaveCrossQuad_r271] using hSrcC
  have hI : t≤actualIncompCaps neatBranchLabeling (crossCap x) (crossCap y) := by
    simpa only [x,a,y,crossCap_interleaveCrossQuad_r271] using
      (T.occupiedParitySample_incomp_r272 j l side u.val htp hOcc)
  have hN := goodCover_independent_on_r261 (htp.trans (T.good j)) l x y
    (htq.trans hDom) hYD (htq.trans hCl) hYC
  have hSmall := noConcreteCrossing_small_r270 neatBranchLabeling (ks j) x y hI hSrcX hN
  have hB : t≤nameBudgetValue true (realBitsName (outputCrossError x y)) (realBitsName (fun _ => ⊥)) (ks j) n :=
    hSmall.trans (iInf_le _ n)
  have hErr (m : ℕ) (hm : m<n) : t⊓membershipBits (realBitsName (outputCrossError x y)) m =
      t⊓membershipBits (realBitsName E) m := by
    simp only [membershipBits_realBitsName_r128]
    have hOC : t⊓crossOutCap c m=t⊓crossOutCap y m :=
      extract4_maskAt_r257 hPre 2 m (hm.trans_le hn)
    have hOP : t⊓crossOutPay c m=t⊓crossOutPay y m :=
      extract4_maskAt_r257 hPre 3 m (hm.trans_le hn)
    have h1 : t⊓H m=t⊓crossOutCap y m := by
      simpa only [c,crossOutCap_interleaveCrossQuad_r271] using hOC
    have h2 : t⊓z m=t⊓crossOutPay y m := by
      simpa only [c,crossOutPay_interleaveCrossQuad_r271] using hOP
    simpa only [E,outputCrossError,x,crossOutCap_interleaveCrossQuad_r271,crossOutPay_interleaveCrossQuad_r271,
      bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement] using
      (mask_xor_congr_r257 (mask_inf_congr_r126 rfl h2.symm) (mask_inf_congr_r126 h1.symm rfl) :
        t⊓(((H m⊓crossOutPay y m)⊓(crossOutCap y m⊓Y m)ᶜ) ⊔
          ((H m⊓crossOutPay y m)ᶜ⊓(crossOutCap y m⊓Y m))) =
        t⊓(((H m⊓z m)⊓(H m⊓Y m)ᶜ)⊔((H m⊓z m)ᶜ⊓(H m⊓Y m))))
  have he := nameBudgetValue_mask_r226 (C := realBitsName (fun _ => ⊥))
    (C' := realBitsName (fun _ => ⊥)) hErr (fun _ _ => rfl) true (ks j)
  exact ⟨t,ht,htr,((le_inf le_rfl hB).trans_eq he).trans inf_le_right⟩

end SetLanguage
end JSP000933
