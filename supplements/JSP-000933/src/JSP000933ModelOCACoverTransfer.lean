import JSP000933ActualOCACodedEdgeMask

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem namedSectionClosed_ext_index_r244 (H A : bSet B) :
    bSet.B_ext (fun i => namedSectionClosed H i A) := by
  intro i j
  exact (namedSectionClosed_index_mask_r178 H A (show (i =ᴮ j) ≤ i =ᴮ j from le_rfl)).le.trans inf_le_right

theorem namedCover_to_goodTable_r244 (D : (ℕ → B) → B) (K : Word × Word → B)
    (hD : RealTestExt D) (p : B) (H : bSet B)
    (hI : p ≤ irreflexiveGraphValue D K) (hS : p ≤ symmetricGraphValue D K)
    (hCov : p ≤ namedCoverValue (profileDomainName D) (graphCodeName K) H) :
    p ≤ goodCoverValue id D K (coverTableOfName H) := by
  let X := profileDomainName D
  let W := graphCodeName K
  let c := coverTableOfName H
  have hM (x : ℕ → B) : (realBitsName x ∈ᴮ X) = D x := profileDomainName_mem_bits_r240 D hD x
  have hCl n (x : ℕ → B) : namedSectionClosed H (bSet.of_nat n) (realBitsName x) =
      ClosedMember c n x := by
    simpa only [c,membershipBits_realBitsName_r128] using
      namedSectionClosed_to_table_r242 H (realBitsName x) n
  refine le_inf ?_ ?_
  · apply le_iInf
    intro x
    apply (le_materialImp_iff_r126 _ _ _).mpr
    have hh : p ≤ imp (realBitsName x ∈ᴮ X)
        (⨆ i : bSet B, (i ∈ᴮ bSet.omega) ⊓ namedSectionClosed H i (realBitsName x)) :=
      hCov.trans (inf_le_left.trans (iInf_le _ (realBitsName x)))
    rw [hM x,omega_exists_r191 _ (namedSectionClosed_ext_index_r244 H (realBitsName x))] at hh
    exact (_root_.context_imp_elim (inf_le_left.trans hh) inf_le_right).trans_eq
      (congrArg iSup (funext (fun n => hCl n x)))
  · apply le_iInf
    intro ix
    obtain ⟨n,x,y⟩ := ix
    apply (le_materialImp_iff_r126 _ _ _).mpr
    let A := realBitsName x
    let Z := realBitsName y
    let i : bSet B := bSet.of_nat n
    let q := p ⊓ ((D x ⊓ D y) ⊓ (ClosedMember c n x ⊓ ClosedMember c n y))
    have hq : q ≤ p := inf_le_left
    have dx : q ≤ D x := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have dy : q ≤ D y := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hx : q ≤ namedSectionClosed H i A :=
      (inf_le_right.trans (inf_le_right.trans inf_le_left)).trans_eq (hCl n x).symm
    have hy : q ≤ namedSectionClosed H i Z :=
      (inf_le_right.trans (inf_le_right.trans inf_le_right)).trans_eq (hCl n y).symm
    have hImpl : p ≤ imp ((i ∈ᴮ bSet.omega) ⊓ ((A ∈ᴮ X) ⊓ ((Z ∈ᴮ X) ⊓
        (namedSectionClosed H i A ⊓ namedSectionClosed H i Z)))) (namedOpenEdgeValue W A Z)ᶜ :=
      hCov.trans (inf_le_right.trans ((iInf_le _ i).trans ((iInf_le _ A).trans (iInf_le _ Z))))
    have hB := _root_.context_imp_elim (hq.trans hImpl)
      (le_inf bSet.omega_definite (le_inf (dx.trans_eq (hM x).symm)
        (le_inf (dy.trans_eq (hM y).symm) (le_inf hx hy))))
    have he := namedOpenEdge_graphCode_mask_r243 D K hI hS hq dx dy
    exact ((le_inf le_rfl hB).trans_eq (mask_compl_congr_r126 he)).trans inf_le_right

theorem namedOCA_goodTable_if_noClique_r244 (D : (ℕ → B) → B) (K : Word × Word → B)
    (hD : RealTestExt D) (p : B) (hO : p ≤ namedCantorOCAValue B)
    (hI : p ≤ irreflexiveGraphValue D K) (hS : p ≤ symmetricGraphValue D K)
    (hNo : ∀ C : bSet B, p ⊓ namedCliqueValue (profileDomainName D) (graphCodeName K) C ≤ ⊥) :
    p ≤ closedCoverExistsValue D K := by
  have h := namedOCA_testDomain_r243 D K p hO
  apply (le_inf le_rfl h).trans
  rw [inf_sup_left]
  apply sup_le
  · rw [inf_iSup_eq]
    exact (iSup_le hNo).trans bot_le
  · rw [inf_iSup_eq]
    apply iSup_le
    intro H
    have hh := namedCover_to_goodTable_r244 D K hD
      (p ⊓ namedCoverValue (profileDomainName D) (graphCodeName K) H) H
      (inf_le_left.trans hI) (inf_le_left.trans hS) inf_le_right
    exact hh.trans (le_iSup _ (coverTableOfName H))

end SetLanguage
end JSP000933
