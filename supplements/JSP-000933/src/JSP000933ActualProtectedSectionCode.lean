import JSP000933ActualSectionTrackCode

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def SectionPatchCertified (b : Bool) (w : Word) (n : ℕ) (v : Word) : Prop :=
  4*(n+v.length)≤w.length ∧ ∀ i<v.length,
    wordBit w (4*(n+i))= !b ∧ wordBit w (4*(n+i)+1)=wordBit v i

noncomputable def protectedSectionCode (K : Word → B) (b : Bool) (w : Word) : B :=
  ⨆ nv : ℕ × Word, crispTruth B (SectionPatchCertified b w nv.1 nv.2)⊓
    (⨅ u : {u : Word // u.length=nv.1}, saturateOpenCode K (u.val++nv.2))

def paddedSectionStart (w : Word) : Word := w++List.replicate (3*w.length) false

theorem paddedSectionStart_length_r295 (w : Word) : (paddedSectionStart w).length=4*w.length := by
  simp only [paddedSectionStart,List.length_append,List.length_replicate]
  omega

theorem appendedSectionPatch_certified_r295 (w v : Word) (b : Bool) :
    SectionPatchCertified b ((paddedSectionStart w)++encodeFixedSectionPatch b v) w.length v := by
  constructor
  · simp only [List.length_append,paddedSectionStart_length_r295,encodeFixedSectionPatch_length_r294]
    omega
  · intro i hi
    let u := paddedSectionStart w
    have hLen : u.length=4*w.length := paddedSectionStart_length_r295 w
    change wordBit (u++encodeFixedSectionPatch b v) (4*(w.length+i))= !b ∧
      wordBit (u++encodeFixedSectionPatch b v) (4*(w.length+i)+1)=wordBit v i
    constructor
    · rw [wordBit_append_after_r294 _ _ _ (by omega),show 4*(w.length+i)-u.length=4*i by omega]
      exact encodeFixedSectionPatch_role_r294 b v i hi
    · rw [wordBit_append_after_r294 _ _ _ (by omega),show 4*(w.length+i)+1-u.length=4*i+1 by omega]
      exact encodeFixedSectionPatch_template_r294 b v i hi

theorem protectedSectionCode_dense_r295 (K : Word → B) (b : Bool) {p : B}
    (hD : DenseOpenNaming p K) : DenseOpenNaming p (protectedSectionCode K b) := by
  intro w
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨r,v,hr,hrq,hPatch⟩ := denseOpen_common_finite_patch_r293 K (boundedWordFinset w.length)
    q hq (hD.restrict_r293 hqp)
  let s := paddedSectionStart w++encodeFixedSectionPatch b v
  have hP : r≤crispTruth B (SectionPatchCertified b s w.length v) := by
    have hCertified : SectionPatchCertified b s w.length v := appendedSectionPatch_certified_r295 w v b
    rw [crispTruth,ite_eq_left hCertified]
    exact le_top
  have hAll : r≤⨅ u : {u : Word // u.length=w.length}, saturateOpenCode K (u.val++v) :=
    le_iInf (fun u => hPatch u.val ((mem_boundedWordFinset_r285 _ _).mpr u.property.le))
  have hs : r≤protectedSectionCode K b s :=
    le_iSup_of_le (w.length,v) (le_inf hP hAll)
  let x := paddedWordBits (B := B) s
  have hS : r≤cylinderValue x s := le_top.trans (paddedWord_in_ownCylinder_r280 s)
  have he : ExtendsWord w s :=
    extendsWord_trans_r216 (extendsWord_append_r292 w _) (extendsWord_append_r292 _ _)
  have hW : r≤cylinderValue x w := hS.trans (cylinderWord_mono_r173 x he)
  have hO : r≤openValue (protectedSectionCode K b) x := le_iSup_of_le s (le_inf hs hS)
  exact ⟨r,hr,hrq,le_iSup_of_le x (le_inf hW hO)⟩

end SetLanguage
end JSP000933
