import JSP000933ActualFaceMasks

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def KeepNamedBlockCertified (b : Bool) (i : ℕ) (u : Word) : Prop :=
  ∀ m∈justSourceBlock i, 4*m<u.length ∧ wordBit u (4*m)=b

noncomputable def keepNamedBlockCode (a : ℕ → B) (b : Bool) (N : ℕ) (u : Word) : B :=
  ⨆ i : {i : ℕ // N≤ i}, actualIncludesBlock a i.val⊓crispTruth B (KeepNamedBlockCertified b i.val u)

theorem extendWord_keeps_block_r306 (w : Word) (b : Bool) (i : ℕ)
    (hI : w.length≤justSourceStart i) : ∃ u : Word, ExtendsWord w u ∧ KeepNamedBlockCertified b i u := by
  let L := justSourceStart (i+1)-w.length
  let v := List.replicate L false
  let u := paddedSectionStart w++encodeFixedSectionPatch (!b) v
  refine ⟨u,extendsWord_trans_r216 (extendsWord_append_r292 w _) (extendsWord_append_r292 _ _),?_⟩
  have hCert : SectionPatchCertified (!b) u w.length v := appendedSectionPatch_certified_r295 w v (!b)
  have hVL : v.length=L := List.length_replicate
  intro m hm
  have hm' : m∈Finset.Ico (justSourceStart i) (justSourceStart (i+1)) := hm
  obtain ⟨hStart,hEnd⟩ := Finset.mem_Ico.mp hm'
  have hLo := hI.trans hStart
  let d := m-w.length
  have hd : w.length+d=m := Nat.add_sub_of_le hLo
  have hD : d<v.length := by
    rw [hVL]
    dsimp only [d,L]
    omega
  have hBound : 4*m<u.length := by have hh := hCert.1; omega
  have hBit := (hCert.2 d hD).1
  rw [hd] at hBit
  exact ⟨hBound,by cases b <;> exact hBit⟩

theorem keepNamedBlockCode_dense_r306 (a : ℕ → B) (b : Bool) (N : ℕ) {p : B}
    (hA : p≤actualLongBlockLarge a) :
    DenseOpenNaming p (keepNamedBlockCode a b N) := by
  intro w
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  let R := max N w.length
  have hY : q≤⨆ i : {i : ℕ // R≤ i}, actualIncludesBlock a i.val :=
    hqp.trans (hA.trans (iInf_le _ R))
  obtain ⟨i,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq _ hY
  have hI : w.length≤justSourceStart i.val := (le_max_right _ _).trans
    (i.property.trans ((Nat.le_add_right i.val 2).trans (justSourceStart_growth i.val)))
  obtain ⟨u,hUW,hCert⟩ := extendWord_keeps_block_r306 w b i.val hI
  let x := paddedWordBits (B := B) u
  have hU : r≤cylinderValue x u := le_top.trans (paddedWord_in_ownCylinder_r280 u)
  have hW := hU.trans (cylinderWord_mono_r173 x hUW)
  have hC : r≤crispTruth B (KeepNamedBlockCertified b i.val u) := by
    simpa only [crispTruth,ite_eq_left hCert] using (le_top : r≤⊤)
  have hK : r≤keepNamedBlockCode a b N u :=
    le_iSup_of_le ⟨i.val,(le_max_left _ _).trans i.property⟩ (le_inf hR hC)
  exact ⟨r,hr,hrq,le_iSup_of_le x (le_inf hW (le_iSup_of_le u (le_inf hK hU)))⟩

theorem keepNamedBlockCode_sound_r306 (a P : ℕ → B) (b : Bool) (N : ℕ)
    {p : B} (h : p≤openValue (keepNamedBlockCode a b N) P) :
    p≤⨆ i : {i : ℕ // N≤ i}, actualIncludesBlock (bitsMeet a (sectionFreeBits P b)) i.val := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨u,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun u : Word => keepNamedBlockCode a b N u⊓cylinderValue P u) (hqp.trans h)
  obtain ⟨i,t,ht,htr,hT⟩ := exists_nonzero_below_choice_r135 r hr
    (fun i : {i : ℕ // N≤ i} => actualIncludesBlock a i.val⊓crispTruth B (KeepNamedBlockCertified b i.val u))
    (hR.trans inf_le_left)
  have hCert : KeepNamedBlockCertified b i.val u := prop_of_le_crisp_nonzero_r190 ht (hT.trans inf_le_right)
  have hU := htr.trans (hR.trans inf_le_right)
  refine ⟨t,ht,htr.trans hrq,le_iSup_of_le i ?_⟩
  unfold actualIncludesBlock
  apply le_iInf
  intro m
  have htA : t≤a m.val := hT.trans (inf_le_left.trans (iInf_le _ m))
  have hm := hCert m.val m.property
  have hB : t⊓P (4*m.val)=t⊓truthBit b := by
    simpa only [paddedWordBits,hm.2] using cylinder_fixes_paddedBits_r258 hU (4*m.val) hm.1
  have hFree : t⊓sectionFreeBits P b m.val=t := by
    cases b
    · simpa [sectionFreeBits,truthBit] using mask_compl_congr_r126 hB
    · simpa [sectionFreeBits,truthBit] using hB
  exact le_inf htA (hFree.symm.le.trans inf_le_right)

end SetLanguage
end JSP000933
