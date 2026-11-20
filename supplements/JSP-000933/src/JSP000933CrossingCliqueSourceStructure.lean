import JSP000933CountableCellEnumeration

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def sourceCrossEq (x y : ℕ → B) : B :=
  realEqValue (bitsMeet (crossCap x) (crossPay y)) (bitsMeet (crossCap y) (crossPay x))

structure CrossingColorTest (G : bSet B) (D : (ℕ → B) → B) (K : Word × Word → B)
    (k : ℕ) (p : B) : Prop where
  domainExt : RealTestExt D
  symm : p ≤ symmetricGraphValue D K
  irr : p≤ irreflexiveGraphValue D K
  graphCap : ∀ x, p ⊓ D x≤graphPairBits G false (crossCap x) (crossOutCap x)
  graphPay : ∀ x, p ⊓ D x≤graphPairBits G false (crossPay x) (crossOutPay x)
  payBelow : ∀ x i, (p ⊓ D x) ⊓ crossPay x i ≤ crossCap x i
  edgeSound : ∀ x y, p ⊓ (D x ⊓ (D y ⊓ colorValue K x y)) ≤
    sourceCrossEq x y ⊓ (smallAllPrefixes true k (outputCrossError x y))ᶜ

theorem sourceCrossEq_of_realEq_r253 {q : B} {x y : ℕ → B} (he : q≤realEqValue x y) :
    q ≤ sourceCrossEq x y :=
  realEqValue_bitsMeet_mask_r251 (extract4_mask_r240 he 0)
    (extract4_mask_r240 (he.trans_eq (realEqValue_symm_r243 x y)) 1)

theorem namedClique_membership_le_domain_r253 {D : (ℕ → B) → B} {K : Word × Word → B}
    (hD : RealTestExt D) {p q : B} {C : bSet B}
    (hC : p≤namedCliqueValue (profileDomainName D) (graphCodeName K) C)
    (x : ℕ → B) (hp : q≤p) (hx : q≤realBitsName x ∈ᴮ C) : q≤D x := by
  have hSub : q≤C ⊆ᴮ profileDomainName D := hp.trans (hC.trans inf_le_left)
  exact (bSet.mem_of_mem_subset hSub hx).trans_eq (profileDomainName_mem_bits_r240 D hD x)

theorem namedClique_distinct_forces_edge_r253 {D : (ℕ → B) → B} {K : Word × Word → B}
    (hD : RealTestExt D) {p q : B} {C : bSet B}
    (hI : p≤ irreflexiveGraphValue D K) (hS : p ≤ symmetricGraphValue D K)
    (hC : p≤namedCliqueValue (profileDomainName D) (graphCodeName K) C)
    (x y : ℕ → B) (hp : q≤p) (hx : q≤realBitsName x ∈ᴮ C) (hy : q≤realBitsName y ∈ᴮ C)
    (hne : q≤(realEqValue x y)ᶜ) : q≤colorValue K x y := by
  let X := profileDomainName D
  let W := graphCodeName K
  let A := realBitsName x
  let Z := realBitsName y
  have hdX := namedClique_membership_le_domain_r253 hD hC x hp hx
  have hdY := namedClique_membership_le_domain_r253 hD hC y hp hy
  have hne' : q≤(A =ᴮ Z)ᶜ := hne.trans_eq (congrArg (fun b : B => bᶜ) (realBitsName_eq_r128 x y).symm)
  have hImpl : p ≤ imp ((A ∈ᴮ C) ⊓ ((Z ∈ᴮ C) ⊓ (A =ᴮ Z)ᶜ)) (namedOpenEdgeValue W A Z) :=
    hC.trans (inf_le_right.trans (inf_le_right.trans ((iInf_le _ A).trans (iInf_le _ Z))))
  have he := _root_.context_imp_elim (hp.trans hImpl) (le_inf hx (le_inf hy hne'))
  exact ((le_inf le_rfl he).trans_eq (namedOpenEdge_graphCode_mask_r243 D K hI hS hp hdX hdY)).trans inf_le_right

theorem namedClique_crossingAgreement_r253 {G : bSet B} {D : (ℕ → B) → B} {K : Word × Word → B}
    {k : ℕ} {p : B} {C : bSet B}
    (T : CrossingColorTest G D K k p)
    (hC : p≤namedCliqueValue (profileDomainName D) (graphCodeName K) C) (x y : ℕ → B) :
    (p ⊓ (realBitsName x ∈ᴮ C)) ⊓ (p ⊓ (realBitsName y ∈ᴮ C)) ≤ sourceCrossEq x y := by
  let q := (p ⊓ (realBitsName x ∈ᴮ C)) ⊓ (p ⊓ (realBitsName y ∈ᴮ C))
  let E := realEqValue x y
  have hp : q≤p := inf_le_left.trans inf_le_left
  have hx : q≤realBitsName x ∈ᴮ C := inf_le_left.trans inf_le_right
  have hy : q≤realBitsName y ∈ᴮ C := inf_le_right.trans inf_le_right
  have hdX := namedClique_membership_le_domain_r253 T.domainExt hC x hp hx
  have hdY := namedClique_membership_le_domain_r253 T.domainExt hC y hp hy
  have he : q⊓Eᶜ≤colorValue K x y :=
    namedClique_distinct_forces_edge_r253 T.domainExt T.irr T.symm hC x y
      (inf_le_left.trans hp) (inf_le_left.trans hx) (inf_le_left.trans hy) inf_le_right
  have hX : q⊓Eᶜ ≤ sourceCrossEq x y :=
    (le_inf (inf_le_left.trans hp) (le_inf (inf_le_left.trans hdX) (le_inf (inf_le_left.trans hdY) he))).trans
      ((T.edgeSound x y).trans inf_le_left)
  calc
    q = q ⊓ (E ⊔ Eᶜ) := by rw [sup_compl_eq_top,inf_top_eq]
    _ = (q⊓E) ⊔ (q⊓Eᶜ) := inf_sup_left _ _ _
    _ ≤ sourceCrossEq x y := sup_le (sourceCrossEq_of_realEq_r253 inf_le_right) hX

end SetLanguage
end JSP000933
