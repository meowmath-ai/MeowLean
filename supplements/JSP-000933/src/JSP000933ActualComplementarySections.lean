import JSP000933ActualProtectedSectionCode

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem cylinder_from_all_wordBit_masks_r296 {p : B} (x : ℕ → B) (u : Word)
    (h : ∀ m<u.length, p⊓x m=p⊓truthBit (wordBit u m)) : p≤cylinderValue x u := by
  unfold cylinderValue
  apply le_iInf
  intro m
  have hBit := (le_bitEq_iff_r126 p _ _).mpr (h m.val m.isLt)
  simpa only [wordBit,dite_eq_left m.isLt,bitEq_truthBit_r175] using hBit

theorem wordBit_append_before_r296 (u v : Word) (m : ℕ) (hm : m<u.length) :
    wordBit (u++v) m=wordBit u m :=
  by simp only [wordBit_eq_getElemOption_r294,List.getElem?_append_left hm]

theorem sectionPoint_patch_mask_r296 {p : B} (P x : ℕ → B) (b : Bool) (s v : Word) (n : ℕ)
    (hP : p≤cylinderValue P s) (hCert : SectionPatchCertified b s n v)
    (i : ℕ) (hi : i<v.length) :
    p⊓actualSectionPoint P b x (n+i)=p⊓truthBit (wordBit v i) := by
  have h0 : 4*(n+i)<s.length := by have h := hCert.1; omega
  have h1 : 4*(n+i)+1<s.length := by have h := hCert.1; omega
  have hRole := cylinder_fixes_paddedBits_r258 hP (4*(n+i)) h0
  have hTemplate := cylinder_fixes_paddedBits_r258 hP (4*(n+i)+1) h1
  have hFree : p⊓P (4*(n+i))=p⊓truthBit (!b) := by
    simpa only [paddedWordBits,(hCert.2 i hi).1] using hRole
  exact (sectionPoint_fixed_mask_r294 P x b (n+i) hFree).trans
    (by simpa only [sectionTemplateBits,paddedWordBits,(hCert.2 i hi).2] using hTemplate)

theorem protectedSectionCode_sound_r296 (K : Word → B) (b : Bool) (P x : ℕ → B)
    {p : B} (hP : p≤openValue (protectedSectionCode K b) P) :
    p≤openValue K (actualSectionPoint P b x) := by
  let Z := actualSectionPoint P b x
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨s,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun s : Word => protectedSectionCode K b s⊓cylinderValue P s) (hqp.trans hP)
  obtain ⟨nv,t,ht,htr,hT⟩ := exists_nonzero_below_choice_r135 r hr
    (fun nv : ℕ × Word => crispTruth B (SectionPatchCertified b s nv.1 nv.2)⊓
      (⨅ u : {u : Word // u.length=nv.1}, saturateOpenCode K (u.val++nv.2))) (hR.trans inf_le_left)
  have hCert : SectionPatchCertified b s nv.1 nv.2 := prop_of_le_crisp_nonzero_r190 ht (hT.trans inf_le_left)
  obtain ⟨u,hu,v,hv,hvt,hU⟩ := exists_decided_initialWord_r136 Z nv.1 t ht
  have hZS : v≤cylinderValue P s := hvt.trans (htr.trans (hR.trans inf_le_right))
  have hzuv : v≤cylinderValue Z (u++nv.2) := by
    apply cylinder_from_all_wordBit_masks_r296
    intro m hm
    by_cases h : m<u.length
    · simpa only [paddedWordBits,wordBit_append_before_r296 u nv.2 m h] using
        (cylinder_fixes_paddedBits_r258 hU m h)
    · let i := m-u.length
      have hi : i<nv.2.length := by simp only [List.length_append] at hm; dsimp only [i]; omega
      have hm' : nv.1+i=m := by dsimp only [i]; omega
      have hTail := sectionPoint_patch_mask_r296 P x b s nv.2 nv.1 hZS hCert i hi
      rw [hm'] at hTail
      rw [wordBit_append_after_r294 u nv.2 m (Nat.le_of_not_gt h)]
      exact hTail
  have hK : v ≤ saturateOpenCode K (u++nv.2) :=
    hvt.trans (hT.trans (inf_le_right.trans (iInf_le (fun z : {z : Word // z.length = nv.1} => saturateOpenCode K (z.val ++ nv.2)) ⟨u,hu⟩)))
  have hO : v≤openValue (saturateOpenCode K) Z := le_iSup_of_le (u++nv.2) (le_inf hK hzuv)
  exact ⟨v,hv,hvt.trans (htr.trans hrq),hO.trans_eq (openValue_saturate_r219 K Z)⟩

theorem exists_actualComplementarySections_r296 (K : ℕ → Word → B) (p : B)
    (hD : ∀ n, DenseOpenNaming p (K n)) :
    ∃ P : ℕ → B, ∀ (n : ℕ) (b : Bool) (x : ℕ → B),
      p≤openValue (K n) (actualSectionPoint P b x) := by
  let dec (i : ℕ) := (Encodable.decode (α := ℕ × Bool) i).getD (0,false)
  let V (i : ℕ) := protectedSectionCode (K (dec i).1) (dec i).2
  obtain ⟨P,_,hP⟩ := exists_namedReal_meeting_denseOpen_r219 p [] V
    (fun i => protectedSectionCode_dense_r295 _ _ (hD (dec i).1))
  refine ⟨P,fun n b x => protectedSectionCode_sound_r296 (K n) b P x ?_⟩
  have h := hP (Encodable.encode (n,b))
  unfold V dec at h
  rw [Encodable.encodek] at h
  exact h

end SetLanguage
end JSP000933
