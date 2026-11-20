import JSP000933MaskCoherentRealSelection

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def NameMapExt (F : (ℕ → B) → ℕ → B) : Prop :=
  ∀ (p : B) (x y : ℕ → B), p≤realEqValue x y → p≤realEqValue (F x) (F y)

noncomputable def exactGraphSelection (G : bSet B) (s : Bool) : (ℕ → B) → ℕ → B :=
  namedLeastChoice (graphPairBits G s)

theorem exactGraphSelection_ext_r310 (G : bSet B) (s : Bool) : NameMapExt (exactGraphSelection G s) := by
  intro p x y he
  exact namedLeastChoice_mask_r309 (graphPairBits G s)
    (fun z => graphPairBits_ext_left_r214 G s z) he

theorem exactGraphSelection_member_r310 (G : bSet B) (s : Bool) {p : B}
    (h : p≤graphTotalSideValue G s) (x : ℕ → B) :
    p≤graphPairBits G s x (exactGraphSelection G s x) :=
  (h.trans (graphTotal_le_bitsExist_r214 G s x)).trans
    (namedLeastChoice_spec_r309 (graphPairBits G s) x (graphPairBits_ext_right_r214 G s x))

theorem actualGraph_has_exactCoherentIso_r310 (p : B) (G : bSet B)
    (hG : p≤graphPairsOnlyValue G⊓(graphTotalSideValue G false⊓
      (graphTotalSideValue G true⊓actualPreserveReflectValue G))) :
    ∃ J : CoherentSelectedIso B p,
      NameMapExt J.toName ∧ NameMapExt J.invName ∧
      (∀ x, p≤graphPairBits G false x (J.toName x)) ∧
      (∀ y, p≤graphPairBits G true y (J.invName y)) := by
  let F := exactGraphSelection G false
  let R := exactGraphSelection G true
  have hF (x : ℕ → B) : p≤graphPairBits G false x (F x) :=
    exactGraphSelection_member_r310 G false (hG.trans (inf_le_right.trans inf_le_left)) x
  have hR (y : ℕ → B) : p≤graphPairBits G true y (R y) :=
    exactGraphSelection_member_r310 G true (hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))) y
  have hP : p≤actualPreserveReflectValue G :=
    hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  let J : CoherentSelectedIso B p := {
    toName := F
    invName := R
    orderMask := fun x y => (le_bitEq_iff_r126 p _ _).mp
      (graph_orderOnSelectedNames_r214 G p hP x y (F x) (F y) (hF x) (hF y))
    inv_ord := by
      intro x
      have h := actualIso_selected_inverseOrd_r229 p G F R hP hF hR x
      exact ⟨h.trans inf_le_left,h.trans inf_le_right⟩
    inv_har := by
      intro y
      have h0 : p≤graphPairBits G false (R y) y := hR y
      have h1 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) y (F (R y)) h0 (hF (R y))
      have h2 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) (F (R y)) y (hF (R y)) h0
      have symm (a b : B) : bitEq a b=bitEq b a := inf_comm _ _
      exact ⟨liveLE_topFromBitEq_r236 (h := true) (g := false) (x := y) (y := F (R y)) (z := R y)
          (h1.trans_eq (symm _ _)),
        liveLE_topFromBitEq_r236 (h := true) (g := false) (x := F (R y)) (y := y) (z := R y)
          (h2.trans_eq (symm _ _))⟩ }
  exact ⟨J,exactGraphSelection_ext_r310 G false,exactGraphSelection_ext_r310 G true,hF,hR⟩

end SetLanguage
end JSP000933
