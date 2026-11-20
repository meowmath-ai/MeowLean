import JSP000933NamedCountabilityFromCells

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure CoherentSelectedIso (B : Type) [NontrivialCompleteBooleanAlgebra B] (p : B) where
  toName : (ℕ → B) → ℕ → B
  invName : (ℕ → B) → ℕ → B
  orderMask : ∀ x y, p ⊓ liveLE false x y = p ⊓ liveLE true (toName x) (toName y)
  inv_ord : ∀ x, LocalEq false p x (invName (toName x))
  inv_har : ∀ y, LocalEq true p y (toName (invName y))

theorem LocalEq.of_stronger_r246 {h : Bool} {p q : B} {a b : ℕ → B}
    (hq : q≤p) (he : LocalEq h p a b) : LocalEq h q a b :=
  ⟨hq.trans he.1,hq.trans he.2⟩

def CoherentSelectedIso.restrict_r246 {p q : B} (F : CoherentSelectedIso B p) (hq : q≤p) :
    SelectedQuotientIso B q where
  toName := F.toName
  invName := F.invName
  order := by
    intro x y
    have h := F.orderMask x y
    constructor
    · intro hx
      exact ((le_inf hq hx).trans_eq h).trans inf_le_right
    · intro hx
      exact ((le_inf hq hx).trans_eq h.symm).trans inf_le_right
  inv_ord x := (F.inv_ord x).of_stronger_r246 hq
  inv_har y := (F.inv_har y).of_stronger_r246 hq

theorem actualGraph_has_coherentSelectedIso_r246 (p : B) (G : bSet B)
    (hG : p ≤ graphPairsOnlyValue G ⊓ (graphTotalSideValue G false ⊓
      (graphTotalSideValue G true ⊓ actualPreserveReflectValue G))) :
    ∃ F : CoherentSelectedIso B p,
      (∀ x, p≤graphPairBits G false x (F.toName x)) ∧
      (∀ y, p≤graphPairBits G true y (F.invName y)) := by
  obtain ⟨F,R,hF,hR,hOrder⟩ := isoValue_has_two_namedSelections_r214 p G hG
  have hP : p ≤ actualPreserveReflectValue G :=
    hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  let J : CoherentSelectedIso B p := {
    toName := F
    invName := R
    orderMask := fun x y => (le_bitEq_iff_r126 p _ _).mp (hOrder x y)
    inv_ord := by
      intro x
      have h := actualIso_selected_inverseOrd_r229 p G F R hP hF hR x
      exact ⟨h.trans inf_le_left,h.trans inf_le_right⟩
    inv_har := by
      intro y
      have h0 : p ≤ graphPairBits G false (R y) y := hR y
      have h1 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) y (F (R y)) h0 (hF (R y))
      have h2 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) (F (R y)) y (hF (R y)) h0
      have symm (a b : B) : bitEq a b = bitEq b a := inf_comm _ _
      exact ⟨liveLE_topFromBitEq_r236 (h := true) (g := false) (x := y) (y := F (R y)) (z := R y)
          (h1.trans_eq (symm _ _)),
        liveLE_topFromBitEq_r236 (h := true) (g := false) (x := F (R y)) (y := y) (z := R y)
          (h2.trans_eq (symm _ _))⟩ }
  exact ⟨J,hF,hR⟩

theorem LocalEq.of_realEq_r246 (h : Bool) {p : B} {x y : ℕ → B}
    (he : p ≤ realEqValue x y) : LocalEq h p x y := by
  have hin (i : ℕ) : p ⊓ membershipBits (realBitsName x) i =
      p ⊓ membershipBits (realBitsName y) i := by
    simpa only [membershipBits_realBitsName_r128] using (le_realEqValue_iff_r126 p x y).mp he i
  constructor
  · apply nameOrder_of_positiveTails_r229
    intro k _
    apply le_iSup_of_le 0
    apply budgetTail_of_forall_r229
    intro n _
    have hEq := nameBudgetValue_mask_r226 (n := n) (A := realBitsName x) (A' := realBitsName x)
      (fun _ _ => rfl) (fun i _ => (hin i).symm) h k
    exact ((le_inf le_rfl (le_top.trans (nameBudgetValue_refl_r228 h (realBitsName x) k n))).trans_eq hEq.symm).trans inf_le_right
  · apply nameOrder_of_positiveTails_r229
    intro k _
    apply le_iSup_of_le 0
    apply budgetTail_of_forall_r229
    intro n _
    have hEq := nameBudgetValue_mask_r226 (n := n) (A := realBitsName y) (A' := realBitsName y)
      (fun _ _ => rfl) (fun i _ => hin i) h k
    exact ((le_inf le_rfl (le_top.trans (nameBudgetValue_refl_r228 h (realBitsName y) k n))).trans_eq hEq.symm).trans inf_le_right

end SetLanguage
end JSP000933
