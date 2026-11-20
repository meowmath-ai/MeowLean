import JSP000933ActualReservedBlockCode

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem dropOutside_of_cylinder_r307 (K : Word → B) (s : Word) (x : ℕ → B)
    {p : B} (hS : p≤cylinderValue x s) (h : p≤openValue (fun u => K u⊔cylinderOutsideCode s u) x) :
    p≤openValue K x := by
  rw [openValue_sup_code_r303,cylinderOutsideCode_value_r303] at h
  let C := cylinderValue x s
  change p≤openValue K x⊔Cᶜ at h
  calc
    p=p⊓(openValue K x⊔Cᶜ) := le_antisymm (le_inf le_rfl h) inf_le_left
    _=(p⊓openValue K x)⊔(p⊓Cᶜ) := inf_sup_left _ _ _
    _≤openValue K x := sup_le inf_le_right
      (((le_inf (inf_le_left.trans hS) inf_le_right).trans_eq inf_compl_eq_bot').trans bot_le)

theorem exists_actual_section_preserving_large_r307 (a : ℕ → B) (s : Word) (K : ℕ → Word → B)
    (b : Bool) {p : B} (hA : p≤actualLongBlockLarge a)
    (hD : ∀ n, DenseWithinCylinder p s (K n)) :
    ∃ P : ℕ → B, p≤actualLongBlockLarge (bitsMeet a (sectionFreeBits P b)) ∧
      ∀ x : ℕ → B, p≤cylinderValue (actualSectionPoint P b x) s ∧
        ∀ n, p≤openValue (K n) (actualSectionPoint P b x) := by
  let V (n : ℕ) (u : Word) := K n u⊔cylinderOutsideCode s u
  let U (i : ℕ) := if i%2=0 then protectedSectionCode (V (i/2)) b else keepNamedBlockCode a b (i/2)
  have hU (i : ℕ) : DenseOpenNaming p (U i) := by
    by_cases he : i%2=0
    · simpa only [U,ite_eq_left he] using (protectedSectionCode_dense_r295 (V (i/2)) b
        ((hD (i/2)).to_global_r303))
    · simpa only [U,ite_eq_right he] using (keepNamedBlockCode_dense_r306 a b (i/2) hA)
  obtain ⟨P,hP,hAll⟩ := exists_namedReal_meeting_denseOpen_r219 p (encodeFixedSectionPatch b s) U hU
  have hC : SectionPatchCertified b (encodeFixedSectionPatch b s) 0 s := by
    simpa [paddedSectionStart] using (appendedSectionPatch_certified_r295 [] s b)
  have hS (x : ℕ → B) : p≤cylinderValue (actualSectionPoint P b x) s :=
    cylinder_from_all_wordBit_masks_r296 _ s
      (fun m hm => by simpa only [zero_add] using
        (sectionPoint_patch_mask_r296 P x b (encodeFixedSectionPatch b s) s 0 hP hC m hm))
  refine ⟨P,?_,fun x => ⟨hS x,fun n => ?_⟩⟩
  · unfold actualLongBlockLarge
    apply le_iInf
    intro N
    have hOdd : (2*N+1)%2≠0 := by omega
    have hDiv : (2*N+1)/2=N := by omega
    have hO : p≤openValue (keepNamedBlockCode a b N) P := by
      simpa only [U,ite_eq_right hOdd,hDiv] using hAll (2*N+1)
    exact keepNamedBlockCode_sound_r306 a P b N hO
  · have hEven : (2*n)%2=0 := by omega
    have hDiv : (2*n)/2=n := by omega
    have hO : p≤openValue (protectedSectionCode (V n) b) P := by
      simpa only [U,ite_eq_left hEven,hDiv] using hAll (2*n)
    exact dropOutside_of_cylinder_r307 (K n) s _ (hS x)
      (protectedSectionCode_sound_r296 (V n) b P x hO)

end SetLanguage
end JSP000933
