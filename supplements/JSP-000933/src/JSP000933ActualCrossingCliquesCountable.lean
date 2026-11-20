import JSP000933CrossingCliqueSourceStructure

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem CrossingColorTest.restrict_r254 {G : bSet B} {D : (ℕ → B) → B} {K : Word × Word → B}
    {k : ℕ} {p q : B} (T : CrossingColorTest G D K k p) (hq : q≤p) :
    CrossingColorTest G D K k q where
  domainExt := T.domainExt
  symm := hq.trans T.symm
  irr := hq.trans T.irr
  graphCap x := (inf_le_inf_right _ hq).trans (T.graphCap x)
  graphPay x := (inf_le_inf_right _ hq).trans (T.graphPay x)
  payBelow x i := (inf_le_inf_right _ (inf_le_inf_right _ hq)).trans (T.payBelow x i)
  edgeSound x y := (inf_le_inf_right _ hq).trans (T.edgeSound x y)

theorem namedClique_crossing_countable_r254 (G : bSet B) {D : (ℕ → B) → B} {K : Word × Word → B}
    {k : ℕ} (hk : k≠0) {p0 p : B} (hp : p≤p0)
    (F : CoherentSelectedIso B p0) (hG : p0≤actualPreserveReflectValue G)
    (hF : ∀ x, p0≤graphPairBits G false x (F.toName x))
    (T : CrossingColorTest G D K k p) (C : bSet B)
    (hC : p≤namedCliqueValue (profileDomainName D) (graphCodeName K) C) :
    p≤weakCountabilityValue C := by
  let w (x : ℕ → B) := p ⊓ (realBitsName x ∈ᴮ C)
  have hw (x : ℕ → B) : w x≤p0 := inf_le_left.trans hp
  have hDom (x : ℕ → B) : w x≤D x :=
    namedClique_membership_le_domain_r253 T.domainExt hC x inf_le_left inf_le_right
  have hCap (x : ℕ → B) : w x≤graphPairBits G false (crossCap x) (crossOutCap x) :=
    (le_inf inf_le_left (hDom x)).trans (T.graphCap x)
  have hPay (x : ℕ → B) : w x≤graphPairBits G false (crossPay x) (crossOutPay x) :=
    (le_inf inf_le_left (hDom x)).trans (T.graphPay x)
  have hBelow (x : ℕ → B) (i : ℕ) : w x ⊓ crossPay x i≤crossCap x i :=
    (inf_le_inf_right _ (le_inf inf_le_left (hDom x))).trans (T.payBelow x i)
  have hCross (x y : ℕ → B) : w x ⊓ w y ≤ sourceCrossEq x y :=
    namedClique_crossingAgreement_r253 T hC x y
  let U := activePayloadUnion w crossPay
  let H := F.toName U
  let cell := crossingCellValue H k
  have hNull (x : ℕ → B) : LocalLE true (w x) (anchoredError H x) (fun _ => ⊥) :=
    activeCrossing_targetError_null_r248 G F hG hF w crossCap crossPay crossOutCap crossOutPay
      hw hCap hPay hBelow hCross x
  have hR : p≤namedAllRealsValue C := by
    apply le_iInf
    intro A
    rw [← _root_.deduction]
    have hSub : p⊓(A ∈ᴮ C) ≤ C ⊆ᴮ profileDomainName D := inf_le_left.trans (hC.trans inf_le_left)
    have hA : p⊓(A ∈ᴮ C) ≤ A ∈ᴮ profileDomainName D := bSet.mem_of_mem_subset hSub inf_le_right
    exact _root_.context_imp_elim
      (le_top.trans ((profileDomainName_allReals_r240 D).trans (iInf_le _ A))) hA
  letI : Countable CrossCellCode := crossCellCode_countable_r252
  apply namedCountable_of_countableCells_r252 C p cell (crossingCell_ext_r251 H k) hR
    (fun x => crossingCells_cover_of_null_r251 H x k hk (hNull x))
  intro i x y
  let q := p ⊓ ((realBitsName x ∈ᴮ C) ⊓ ((realBitsName y ∈ᴮ C) ⊓ (cell i x ⊓ cell i y)))
  let E := realEqValue x y
  have eq : q≤p := inf_le_left
  have ex : q≤realBitsName x ∈ᴮ C := inf_le_right.trans inf_le_left
  have ey : q≤realBitsName y ∈ᴮ C := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have cx : q≤cell i x := inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have cy : q≤cell i y := inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have hSmall : q ≤ smallAllPrefixes true k (outputCrossError x y) :=
    crossingCells_pairError_small_r251 H x y k i cx cy
  have hx : q≤D x := namedClique_membership_le_domain_r253 T.domainExt hC x eq ex
  have hy : q≤D y := namedClique_membership_le_domain_r253 T.domainExt hC y eq ey
  have he : q⊓Eᶜ≤colorValue K x y :=
    namedClique_distinct_forces_edge_r253 T.domainExt T.irr T.symm hC x y
      (inf_le_left.trans eq) (inf_le_left.trans ex) (inf_le_left.trans ey) inf_le_right
  have hBad : q⊓Eᶜ≤(smallAllPrefixes true k (outputCrossError x y))ᶜ :=
    (le_inf (inf_le_left.trans eq) (le_inf (inf_le_left.trans hx) (le_inf (inf_le_left.trans hy) he))).trans
      ((T.edgeSound x y).trans inf_le_right)
  have hDis : Disjoint q Eᶜ := disjoint_iff_inf_le.mpr
    ((le_inf (inf_le_left.trans hSmall) hBad).trans_eq inf_compl_eq_bot')
  exact (le_compl_iff_disjoint_right.mpr hDis).trans_eq (compl_compl _)

theorem actualOCA_crossing_independentCover_r254 (G : bSet B) {D : (ℕ → B) → B} {K : Word × Word → B}
    {k : ℕ} (hk : k≠0) {p : B} (F : CoherentSelectedIso B p)
    (hOCA : p≤namedCantorOCAValue B) (hG : p≤actualPreserveReflectValue G)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (T : CrossingColorTest G D K k p) : p≤closedCoverExistsValue D K := by
  apply namedOCA_goodTable_if_noClique_r244 D K T.domainExt p hOCA T.irr T.symm
  intro C
  let q := p ⊓ namedCliqueValue (profileDomainName D) (graphCodeName K) C
  have hCnt : q≤weakCountabilityValue C :=
    namedClique_crossing_countable_r254 G hk (show q≤p from inf_le_left) F hG hF
      (T.restrict_r254 inf_le_left) C inf_le_right
  have hUnc : q≤(weakCountabilityValue C)ᶜ := inf_le_right.trans (inf_le_right.trans inf_le_left)
  exact (le_inf hCnt hUnc).trans_eq inf_compl_eq_bot'

end SetLanguage
end JSP000933
