import JSP000933SimultaneousActualCoverCode
import JSP000933NeatFamily

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nonzero_truthBit_mask_injective_r263 {p : B} (hp : p≠⊥) {a b : Bool}
    (h : p⊓truthBit a=p⊓truthBit b) : a=b := by
  cases a <;> cases b
  · rfl
  · exact (hp (by simpa [truthBit]
      using h.symm)).elim
  · exact (hp (by simpa [truthBit]
      using h)).elim
  · rfl

theorem overlappingCylinders_wordBit_eq_r263 {p : B} (hp : p≠⊥) (x : ℕ → B)
    {u v : Word} (hu : p≤cylinderValue x u) (hv : p≤cylinderValue x v)
    (m : ℕ) (hmu : m<u.length) (hmv : m<v.length) : wordBit u m=wordBit v m :=
  nonzero_truthBit_mask_injective_r263 hp
    ((cylinder_fixes_paddedBits_r258 hu m hmu).symm.trans (cylinder_fixes_paddedBits_r258 hv m hmv))

theorem own_binaryPrefixList_r263 (u : Word) : binaryPrefixList (wordBit u) u.length=u := by
  unfold binaryPrefixList
  apply List.ext_getElem List.length_ofFn
  intro m h₁ h₂
  simp only [List.getElem_ofFn,wordBit,dite_eq_left h₂]

theorem overlappingCylinders_getPrefix_r263 {p : B} (hp : p≠⊥) (x : ℕ → B)
    {u v : Word} (hu : p≤cylinderValue x u) (hv : p≤cylinderValue x v)
    (hLen : u.length≤v.length) : u=binaryPrefixList (wordBit v) u.length := by
  refine (own_binaryPrefixList_r263 u).symm.trans ?_
  unfold binaryPrefixList
  apply List.ext_getElem (by simp only [List.length_ofFn])
  intro m hm hm'
  have hmU : m<u.length := by simpa only [List.length_ofFn] using hm
  simpa only [List.getElem_ofFn] using
    (overlappingCylinders_wordBit_eq_r263 hp x hu hv m hmU (hmU.trans_le hLen))

noncomputable def actualBranchBits (x : ℕ → B) (m : ℕ) : B :=
  ⨆ w : {w : Word // m∈justSourceBlock (Encodable.encode w)}, cylinderValue x w.1

theorem cylinder_sourceBlock_in_actualBranch_r263 (x : ℕ → B) (u : Word)
    (m : ℕ) (hm : m∈justSourceBlock (Encodable.encode u)) :
    cylinderValue x u≤actualBranchBits x m :=
  le_iSup (fun w : {w : Word // m∈justSourceBlock (Encodable.encode w)} => cylinderValue x w.1) ⟨u,hm⟩

theorem actualBranchBits_mask_r263 {p : B} {x y : ℕ → B}
    (he : p≤realEqValue x y) : p≤realEqValue (actualBranchBits x) (actualBranchBits y) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  unfold actualBranchBits
  exact mask_iSup_congr_r126 (fun w => mask_cylinder_congr_r127 he w.1)

theorem actualBranch_neat_r263 (x : ℕ → B) :
    (⊤ : B) ≤ capNeatValue ⟨neatBlockLabel, neatBlockLabel_injective⟩ (actualBranchBits x) := by
  unfold capNeatValue
  apply le_iInf
  intro m
  apply le_iInf
  intro n
  change (⊤ : B)≤(actualBranchBits x m⊓actualBranchBits x n)ᶜ ⊔
    crispTruth B (labelsComparable (neatBlockLabel m) (neatBlockLabel n))
  apply (le_materialImp_iff_r126 _ _ _).mpr
  rw [top_inf_eq]
  apply le_of_dense_named_refinements_r219
  intro p hp hP
  obtain ⟨u,s,hs,hsp,hU⟩ := exists_nonzero_below_choice_r135 p hp
    (fun w : {w : Word // m∈justSourceBlock (Encodable.encode w)} => cylinderValue x w.1)
    (hP.trans inf_le_left)
  obtain ⟨v,t,ht,hts,hV⟩ := exists_nonzero_below_choice_r135 s hs
    (fun w : {w : Word // n∈justSourceBlock (Encodable.encode w)} => cylinderValue x w.1)
    (hsp.trans (hP.trans inf_le_right))
  have hU' := hts.trans hU
  have hComp : labelsComparable (neatBlockLabel m) (neatBlockLabel n) := by
    rcases le_total u.val.length v.val.length with h | h
    · have h₁ : m∈branchLargeSet (wordBit v.val) := by
        refine ⟨u.val.length,?_⟩
        change m∈justSourceBlock (Encodable.encode (binaryPrefixList (wordBit v.val) u.val.length))
        rw [← overlappingCylinders_getPrefix_r263 ht x hU' hV h]
        exact u.property
      have h₂ : n∈branchLargeSet (wordBit v.val) := by
        refine ⟨v.val.length,?_⟩
        change n∈justSourceBlock (Encodable.encode (binaryPrefixList (wordBit v.val) v.val.length))
        rw [own_binaryPrefixList_r263 v.val]
        exact v.property
      exact branch_labels_comparable (wordBit v.val) h₁ h₂
    · have h₁ : m∈branchLargeSet (wordBit u.val) := by
        refine ⟨u.val.length,?_⟩
        change m∈justSourceBlock (Encodable.encode (binaryPrefixList (wordBit u.val) u.val.length))
        rw [own_binaryPrefixList_r263 u.val]
        exact u.property
      have h₂ : n∈branchLargeSet (wordBit u.val) := by
        refine ⟨v.val.length,?_⟩
        change n∈justSourceBlock (Encodable.encode (binaryPrefixList (wordBit u.val) v.val.length))
        rw [← overlappingCylinders_getPrefix_r263 ht x hV hU' h]
        exact v.property
      exact branch_labels_comparable (wordBit u.val) h₁ h₂
  exact ⟨t,ht,hts.trans hsp,by simpa only [crispTruth,ite_eq_left hComp] using (le_top : t≤⊤)⟩

end SetLanguage
end JSP000933
