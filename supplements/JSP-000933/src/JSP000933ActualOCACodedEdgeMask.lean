import JSP000933ArbitraryClosedCodeDecoding
import JSP000933NamedOCATop

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem realEqValue_symm_r243 (x y : ℕ → B) : realEqValue x y = realEqValue y x := by
  unfold realEqValue
  exact congrArg iInf (funext (fun i => inf_comm _ _))

theorem namedOpenEdge_graphCode_mask_r243 (D : (ℕ → B) → B) (K : Word × Word → B)
    {p q : B} (hI : p ≤ irreflexiveGraphValue D K) (hS : p ≤ symmetricGraphValue D K)
    {x y : ℕ → B} (hqp : q≤p) (hx : q≤D x) (hy : q≤D y) :
    q ⊓ namedOpenEdgeValue (graphCodeName K) (realBitsName x) (realBitsName y) =
      q ⊓ colorValue K x y := by
  rw [namedOpenEdge_graphCode_r241]
  let C := colorValue K x y
  let C' := colorValue K y x
  let E := realEqValue x y
  have hN : q ⊓ C ≤ Eᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    let r := (q ⊓ C) ⊓ E
    have hR : r ≤ realEqValue x x :=
      (le_realEqValue_iff_r126 _ _ _).mpr (fun _ => rfl)
    have hE : r ≤ realEqValue y x := inf_le_right.trans_eq (realEqValue_symm_r243 x y)
    have hh := mask_colorValue_congr_r127 K hR hE
    have hCol : r ≤ colorValue K x x :=
      ((le_inf le_rfl (inf_le_left.trans inf_le_right)).trans_eq hh).trans inf_le_right
    have hi : p ≤ (D x)ᶜ ⊔ (colorValue K x x)ᶜ := hI.trans (iInf_le _ x)
    have hNot : r ≤ (colorValue K x x)ᶜ :=
      (le_inf (inf_le_left.trans (inf_le_left.trans hqp))
        (inf_le_left.trans (inf_le_left.trans hx))).trans ((le_materialImp_iff_r126 _ _ _).mp hi)
    exact (le_inf hCol hNot).trans_eq inf_compl_eq_bot'
  have hSym : q ⊓ C' ≤ C := by
    have h : p ≤ ((D y ⊓ D x) ⊓ C')ᶜ ⊔ C :=
      hS.trans ((iInf_le _ y).trans (iInf_le _ x))
    exact (le_inf (inf_le_left.trans hqp)
      (le_inf (le_inf (inf_le_left.trans hy) (inf_le_left.trans hx)) inf_le_right)).trans
        ((le_materialImp_iff_r126 _ _ _).mp h)
  apply le_antisymm
  · apply le_inf inf_le_left
    have h : q ⊓ (C ⊔ C') ≤ C := by
      rw [inf_sup_left]
      exact sup_le inf_le_right hSym
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans h
  · exact le_inf inf_le_left (le_inf hN (inf_le_right.trans le_sup_left))

theorem namedOCA_testDomain_r243 (D : (ℕ → B) → B) (K : Word × Word → B) (p : B)
    (hOCA : p ≤ namedCantorOCAValue B) :
    p ≤ (⨆ C : bSet B, namedCliqueValue (profileDomainName D) (graphCodeName K) C) ⊔
      (⨆ H : bSet B, namedCoverValue (profileDomainName D) (graphCodeName K) H) := by
  have h := hOCA.trans ((iInf_le _ (profileDomainName D)).trans (iInf_le _ (graphCodeName K)))
  exact _root_.context_imp_elim h (le_top.trans (profileDomainName_allReals_r240 D))

end SetLanguage
end JSP000933
