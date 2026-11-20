import JSP000933ActualFiniteCommonPatch

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def sectionFreeBits (P : ℕ → B) (b : Bool) (m : ℕ) : B :=
  if b then P (4*m) else (P (4*m))ᶜ

def sectionTemplateBits (P : ℕ → B) (m : ℕ) : B := P (4*m+1)

def actualSectionPoint (P : ℕ → B) (b : Bool) (x : ℕ → B) (m : ℕ) : B :=
  (sectionFreeBits P b m⊓x m)⊔((sectionFreeBits P b m)ᶜ⊓sectionTemplateBits P m)

theorem wordBit_eq_getElemOption_r294 (u : Word) (m : ℕ) :
    wordBit u m=(u[m]?).getD false :=
  (List.getD_getElem? (l := u) (i := m) (d := false)).symm

theorem wordBit_append_after_r294 (u v : Word) (m : ℕ) (hm : u.length≤ m) :
    wordBit (u++v) m=wordBit v (m-u.length) := by
  simp only [wordBit_eq_getElemOption_r294,List.getElem?_append_right hm]

def encodeFixedSectionPatch (b : Bool) (v : Word) : Word :=
  List.ofFn (n := 4*v.length) (fun i =>
    if i.val%4=0 then !b else if i.val%4=1 then wordBit v (i.val/4) else false)

@[simp] theorem encodeFixedSectionPatch_length_r294 (b : Bool) (v : Word) :
    (encodeFixedSectionPatch b v).length=4*v.length := List.length_ofFn

theorem encodeFixedSectionPatch_role_r294 (b : Bool) (v : Word) (i : ℕ) (hi : i<v.length) :
    wordBit (encodeFixedSectionPatch b v) (4*i)=!b := by
  rw [wordBit_eq_getElemOption_r294,encodeFixedSectionPatch,List.getElem?_ofFn,dite_eq_left (by omega)]
  have hm : (4*i)%4=0 := by omega
  simp [hm]

theorem encodeFixedSectionPatch_template_r294 (b : Bool) (v : Word) (i : ℕ) (hi : i<v.length) :
    wordBit (encodeFixedSectionPatch b v) (4*i+1)=wordBit v i := by
  rw [wordBit_eq_getElemOption_r294,encodeFixedSectionPatch,List.getElem?_ofFn,dite_eq_left (by omega)]
  have hm : (4*i+1)%4=1 := by omega
  have hd : (4*i+1)/4=i := by omega
  simp [hm,hd]

theorem sectionPoint_fixed_mask_r294 {p : B} (P x : ℕ → B) (b : Bool) (m : ℕ)
    (h : p⊓P (4*m)=p⊓truthBit (!b)) :
    p⊓actualSectionPoint P b x m=p⊓sectionTemplateBits P m := by
  have hFree : p⊓sectionFreeBits P b m=p⊓(⊥ : B) := by
    cases b
    · simpa [sectionFreeBits,truthBit] using mask_compl_congr_r126 h
    · simpa [sectionFreeBits,truthBit] using h
  have hF := mask_sup_congr_r211 (mask_inf_congr_r126 hFree (show p⊓x m=p⊓x m from rfl))
    (mask_inf_congr_r126 (mask_compl_congr_r126 hFree)
      (show p⊓sectionTemplateBits P m=p⊓sectionTemplateBits P m from rfl))
  simpa [actualSectionPoint] using hF

end SetLanguage
end JSP000933
