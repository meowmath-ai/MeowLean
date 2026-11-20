import JSP000933ActualMaskedInputRectangles

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualSideCode {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (j l : ℕ) (side : Bool) : Word × Word → B :=
  let a := actualParityCap T.freshCap j side
  meetInputBinaryCode (actualSampleTreeBinaryCode T j l side a (F.toName a)) a

noncomputable def actualSideApprox {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (j l : ℕ) (side : Bool) (x : ℕ → B) : ℕ → B :=
  bitsMeet (F.toName (actualParityCap T.freshCap j side)) (actualLexSelector (actualSideCode T F j l side) x)

theorem actualSideCode_tree_r288 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (j l : ℕ) (side : Bool) (x z : ℕ → B) :
    (colorValue (actualSideCode T F j l side) x z)ᶜ=
      fixedActualSampleTree T j l side (interleaveCrossQuad (actualParityCap T.freshCap j side)
        (bitsMeet (actualParityCap T.freshCap j side) x) (F.toName (actualParityCap T.freshCap j side)) z) := by
  unfold actualSideCode
  rw [meetInputBinaryCode_value_r287,actualSampleTree_binaryClosed_r276]

theorem actualSideGenuine_in_domain_r288 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (j : ℕ) (side : Bool) (x : ℕ → B) :
    let a := actualParityCap T.freshCap j side
    let b := bitsMeet a x
    p≤namedBranchCrossDomain G (interleaveCrossQuad a b (F.toName a) (F.toName b)) := by
  let a := actualParityCap T.freshCap j side
  let b := bitsMeet a x
  let w := interleaveCrossQuad a b (F.toName a) (F.toName b)
  change p≤namedBranchCrossDomain G w
  have hI : p≤actualUnboundedCap a :=
    le_top.trans (actualParityCap_unbounded_r268 (actualFreshBranch T.support) j side)
  have hA : p≤bitsBelowValue a T.freshCap :=
    bitsBelowValue_of_pointwise_r272 (actualParityCap_le_r268 _ _ _)
  have hN : p≤capNeatValue neatBranchLabeling a :=
    capNeatValue_of_below_r264 _ hA (le_top.trans (actualBranch_neat_r263 (actualFreshBranch T.support)))
  have hB : p≤bitsBelowValue b a := bitsBelowValue_of_pointwise_r272 (fun _ => inf_le_left)
  have hEx : p≤branchCapExtra a := le_inf hI (le_iSup_of_le (actualFreshBranch T.support) hA)
  unfold namedBranchCrossDomain concreteCrossDomain
  simp only [w,crossCap_interleaveCrossQuad_r271,crossPay_interleaveCrossQuad_r271,
    crossOutCap_interleaveCrossQuad_r271,crossOutPay_interleaveCrossQuad_r271]
  exact le_inf hEx (le_inf hN (le_inf hB (le_inf (hF a) (hF b))))

theorem actualSide_countableApprox_r288 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (j : ℕ) (side : Bool) (x : ℕ → B) :
    let a := actualParityCap T.freshCap j side
    let b := bitsMeet a x
    p≤⨆ l : ℕ, smallAllPrefixes true (ks j)
      (bitsSymmDiff (actualSideApprox T F j l side x) (bitsMeet (F.toName a) (F.toName b))) := by
  let a := actualParityCap T.freshCap j side
  let b := bitsMeet a x
  let H := F.toName a
  let Y := F.toName b
  let w := interleaveCrossQuad a b H Y
  have hD : p≤namedBranchCrossDomain G w := actualSideGenuine_in_domain_r288 T F hF j side x
  have hU : p≤⨆ l : ℕ, ClosedMember (T.cover j) l w :=
    _root_.context_imp_elim ((T.good j).trans (inf_le_left.trans (iInf_le _ w))) hD
  change p≤⨆ l : ℕ, smallAllPrefixes true (ks j)
    (bitsSymmDiff (actualSideApprox T F j l side x) (bitsMeet H Y))
  apply (le_inf le_rfl hU).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro l
  let q := p⊓ClosedMember (T.cover j) l w
  let K := actualSideCode T F j l side
  have hq : q≤p := inf_le_left
  have hC : q≤ClosedMember (T.cover j) l w := inf_le_right
  have hTree := fixedActualSampleTree_intro_r271 T j l side w (hq.trans hD) hC
  have hXY : q≤(colorValue K x Y)ᶜ := hTree.trans_eq (actualSideCode_tree_r288 T F j l side x Y).symm
  have hNil : q≤cylinderValue Y [] := by
    unfold cylinderValue
    exact le_iInf (fun i => Fin.elim0 i)
  have hFeas : q≤actualFiberFeasible K x [] := le_iSup_of_le Y (le_inf hNil hXY)
  have hL := (hFeas.trans (actualLexSelector_closed_r284 K x)).trans_eq
    (actualSideCode_tree_r288 T F j l side x (actualLexSelector K x))
  have hB := actual_masked_sampleTree_small_r273 T j l side b H Y (actualLexSelector K x) hq
    (hq.trans hD) hC hL
  exact le_iSup_of_le l hB

end SetLanguage
end JSP000933
