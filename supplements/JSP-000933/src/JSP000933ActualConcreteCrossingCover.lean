import JSP000933ConcreteCrossingColorLaws

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def concreteCrossDomain (e : ℕ ↪ Word) (G : bSet B)
    (extra : (ℕ → B) → B) (x : ℕ → B) : B :=
  extra (crossCap x) ⊓ (capNeatValue e (crossCap x) ⊓
    (bitsBelowValue (crossPay x) (crossCap x) ⊓
      (graphPairBits G false (crossCap x) (crossOutCap x) ⊓ graphPairBits G false (crossPay x) (crossOutPay x))))

theorem concreteCrossDomain_ext_r260 (e : ℕ ↪ Word) (G : bSet B)
    (extra : (ℕ → B) → B) (hE : RealTestExt extra) : RealTestExt (concreteCrossDomain e G extra) := by
  intro p x y h
  have hc : p≤realEqValue (crossCap x) (crossCap y) := extract4_mask_r240 h 0
  have hb : p≤realEqValue (crossPay x) (crossPay y) := extract4_mask_r240 h 1
  have hd : p≤realEqValue (crossOutCap x) (crossOutCap y) := extract4_mask_r240 h 2
  have hf : p≤realEqValue (crossOutPay x) (crossOutPay y) := extract4_mask_r240 h 3
  have hCD := (graphPairBits_ext_left_r214 G false (crossOutCap x) p _ _ hc).trans
    (graphPairBits_ext_right_r214 G false (crossCap y) p _ _ hd)
  have hBF := (graphPairBits_ext_left_r214 G false (crossOutPay x) p _ _ hb).trans
    (graphPairBits_ext_right_r214 G false (crossPay y) p _ _ hf)
  exact mask_inf_congr_r126 (hE p _ _ hc) (mask_inf_congr_r126 (capNeatValue_mask_r256 e hc)
    (mask_inf_congr_r126 (bitsBelowValue_mask_r256 hb hc) (mask_inf_congr_r126 hCD hBF)))

theorem concreteCrossDomain_neat_r260 (e : ℕ ↪ Word) (G : bSet B)
    (extra : (ℕ → B) → B) (x : ℕ → B) :
    concreteCrossDomain e G extra x≤capNeatValue e (crossCap x) := inf_le_right.trans inf_le_left

theorem concreteCrossDomain_below_r260 (e : ℕ ↪ Word) (G : bSet B)
    (extra : (ℕ → B) → B) (x : ℕ → B) :
    concreteCrossDomain e G extra x≤bitsBelowValue (crossPay x) (crossCap x) :=
  inf_le_right.trans (inf_le_right.trans inf_le_left)

theorem concreteCrossColorValue_irrGraph_r260 (e : ℕ ↪ Word) (k : ℕ) (G : bSet B)
    (extra : (ℕ → B) → B) :
    (⊤ : B) ≤ irreflexiveGraphValue (concreteCrossDomain e G extra) (concreteCrossColorTable e k) := by
  unfold irreflexiveGraphValue
  apply le_iInf
  intro x
  apply (le_materialImp_iff_r126 _ _ _).mpr
  rw [top_inf_eq]
  exact le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr
    (concreteCrossColorValue_noLoop_r259 e k x (concreteCrossDomain_neat_r260 e G extra x)))

theorem concreteCrossColorTest_r260 (e : ℕ ↪ Word) (k : ℕ) (G : bSet B)
    (extra : (ℕ → B) → B) (hE : RealTestExt extra) (p : B) :
    CrossingColorTest G (concreteCrossDomain e G extra) (concreteCrossColorTable e k) k p where
  domainExt := concreteCrossDomain_ext_r260 e G extra hE
  symm := le_top.trans (concreteCrossColorValue_symmGraph_r259 e k _)
  irr := le_top.trans (concreteCrossColorValue_irrGraph_r260 e k G extra)
  graphCap x := inf_le_right.trans (inf_le_right.trans
    (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  graphPay x := inf_le_right.trans (inf_le_right.trans
    (inf_le_right.trans (inf_le_right.trans inf_le_right)))
  payBelow x i := bitsBelowValue_apply_r256
    (inf_le_right.trans (concreteCrossDomain_below_r260 e G extra x)) i
  edgeSound x y := by
    let D := concreteCrossDomain e G extra
    let q := p ⊓ (D x ⊓ D y)
    have dx : q≤D x := inf_le_right.trans inf_le_left
    have dy : q≤D y := inf_le_right.trans inf_le_right
    have h := concreteCrossColorValue_edge_r259 e k x y
      (dx.trans (concreteCrossDomain_neat_r260 e G extra x))
      (dy.trans (concreteCrossDomain_neat_r260 e G extra y))
      (dx.trans (concreteCrossDomain_below_r260 e G extra x))
      (dy.trans (concreteCrossDomain_below_r260 e G extra y))
    exact (le_inf (le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))))
        (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans h

theorem actualOCA_concrete_crossing_cover_r260 (G : bSet B) (e : ℕ ↪ Word) (k : ℕ) (hk : k≠0)
    (extra : (ℕ → B) → B) (hE : RealTestExt extra) {p : B} (F : CoherentSelectedIso B p)
    (hOCA : p≤namedCantorOCAValue B) (hG : p≤actualPreserveReflectValue G)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x)) :
    p≤closedCoverExistsValue (concreteCrossDomain e G extra) (concreteCrossColorTable e k) :=
  actualOCA_crossing_independentCover_r254 G hk F hOCA hG hF (concreteCrossColorTest_r260 e k G extra hE p)

end SetLanguage
end JSP000933
