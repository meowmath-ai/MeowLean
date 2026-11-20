import JSP000933ActualMaskedSampleTreeError

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem equalLength_cylinders_disjoint_r274 (x : ℕ → B) {u v : Word}
    (hlen : u.length=v.length) (hne : u≠v) : cylinderValue x u⊓cylinderValue x v≤⊥ := by
  let t := cylinderValue x u⊓cylinderValue x v
  by_contra h
  have ht : t≠⊥ := fun he => h he.le
  have he := overlappingCylinders_getPrefix_r263 ht x
    (show t≤cylinderValue x u from inf_le_left) (show t≤cylinderValue x v from inf_le_right) hlen.le
  exact hne (he.trans ((congrArg (binaryPrefixList (wordBit v)) hlen).trans (own_binaryPrefixList_r263 v)))

noncomputable def missingActualSamplePrefix {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l k : ℕ) (u : Word) : B :=
  if u.length=4*actualSampleCut j k then
    (closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u)ᶜ else ⊥

theorem allowedActualSamplePrefix_eq_compl_open_r274 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l k : ℕ) (x : ℕ → B) :
    allowedActualSamplePrefix T j l k x=(openValue (missingActualSamplePrefix T j l k) x)ᶜ := by
  classical
  let N := 4*actualSampleCut j k
  let P (u : Word) := closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u
  let K := missingActualSamplePrefix T j l k
  apply le_antisymm
  · apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    change ((⨆ u : {u : Word // u.length=N}, P u.val⊓cylinderValue x u.val) ⊓
      (⨆ v : Word, K v⊓cylinderValue x v))≤⊥
    rw [iSup_inf_iSup]
    apply iSup_le
    rintro ⟨u,v⟩
    by_cases hv : v.length=N
    · have hK : K v=(P v)ᶜ := by simp only [K,P,N,missingActualSamplePrefix,ite_eq_left hv]
      rw [hK]
      by_cases he : u.val=v
      · rw [he]
        exact ((le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)).trans_eq
          inf_compl_eq_bot')
      · exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans
          (equalLength_cylinders_disjoint_r274 x (u.property.trans hv.symm) he)
    · have hK : K v=⊥ := by simp only [K,N,missingActualSamplePrefix,ite_eq_right hv]
      rw [hK,bot_inf_eq,inf_bot_eq]
  · apply le_of_dense_named_refinements_r219
    intro q hq hQ
    obtain ⟨u,hu,t,ht,htq,hT⟩ := exists_decided_initialWord_r136 x N q hq
    have hK : K u=(P u)ᶜ := by simp only [K,P,N,missingActualSamplePrefix,ite_eq_left hu]
    have hBad : t⊓(P u)ᶜ≤openValue K x :=
      le_iSup_of_le u (le_inf (inf_le_right.trans_eq hK.symm) (inf_le_left.trans hT))
    have hBot : t⊓(P u)ᶜ≤⊥ :=
      (le_inf hBad (inf_le_left.trans (htq.trans hQ))).trans_eq inf_compl_eq_bot'
    have hP : t≤P u :=
      (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hBot)).trans_eq (compl_compl _)
    exact ⟨t,ht,htq,le_iSup_of_le ⟨u,hu⟩ (le_inf hP hT)⟩

theorem openValue_iSup_code_r274 {I : Type} (K : I → Word → B) (x : ℕ → B) :
    openValue (fun u => ⨆ i, K i u) x=⨆ i, openValue (K i) x := by
  simp only [openValue,iSup_inf_eq]
  rw [iSup_comm]

noncomputable def missingActualSampleTree {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (u : Word) : B :=
  ⨆ k : {k : ℕ // l≤k ∧ k%2≠colorParity side}, missingActualSamplePrefix T j l k.val u

theorem fixedActualSampleTree_eq_compl_open_r274 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (x : ℕ → B) :
    fixedActualSampleTree T j l side x=(openValue (missingActualSampleTree T j l side) x)ᶜ := by
  have he : fixedActualSampleTree T j l side x =
      ⨅ k : {k : ℕ // l≤k ∧ k%2≠colorParity side}, allowedActualSamplePrefix T j l k.val x := by
    apply le_antisymm
    · exact le_iInf (fun k => fixedActualSampleTree_apply_r271 T j l side x le_rfl k.val k.2.1 k.2.2)
    · unfold fixedActualSampleTree
      exact le_iInf (fun k => le_iInf (fun hl => le_iInf (fun hs =>
        iInf_le (fun m : {m : ℕ // l ≤ m ∧ m % 2 ≠ colorParity side} =>
          allowedActualSamplePrefix T j l m.val x) ⟨k,hl,hs⟩)))
  rw [he]
  let K := fun k : {k : ℕ // l ≤ k ∧ k % 2 ≠ colorParity side} =>
    missingActualSamplePrefix T j l k.val
  change _ = (openValue (fun u => ⨆ k, K k u) x)ᶜ
  rw [openValue_iSup_code_r274 K x,compl_iSup]
  apply congrArg iInf
  funext k
  exact allowedActualSamplePrefix_eq_compl_open_r274 T j l k.val x

end SetLanguage
end JSP000933
