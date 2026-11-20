import JSP000933ActualQuotientLatticeLaws

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def LocalLE (h : Bool) (p : B) (x y : ℕ → B) : Prop := p ≤ liveLE h x y

def LocalEq (h : Bool) (p : B) (x y : ℕ → B) : Prop :=
  LocalLE h p x y ∧ LocalLE h p y x

theorem LocalLE.refl_r236 (h : Bool) (p : B) (x : ℕ → B) : LocalLE h p x x :=
  le_top.trans (nameOrderValue_refl_r229 h (realBitsName x))

theorem LocalLE.trans_r236 {h : Bool} {p : B} {x y z : ℕ → B}
    (a : LocalLE h p x y) (b : LocalLE h p y z) : LocalLE h p x z :=
  (le_inf a b).trans (nameOrderValue_trans_r229 h _ _ _)

theorem LocalEq.symm_r236 {h : Bool} {p : B} {x y : ℕ → B} (a : LocalEq h p x y) : LocalEq h p y x :=
  ⟨a.2,a.1⟩

theorem LocalEq.trans_r236 {h : Bool} {p : B} {x y z : ℕ → B}
    (a : LocalEq h p x y) (b : LocalEq h p y z) : LocalEq h p x z :=
  ⟨a.1.trans_r236 b.1,b.2.trans_r236 a.2⟩

theorem LocalLE.of_eq_forward_r236 {h : Bool} {p : B} {x y : ℕ → B} (a : x=y) :
    LocalLE h p x y := by
  subst y
  exact LocalLE.refl_r236 h p x

theorem LocalLE.meet_right_r236 {h : Bool} {p : B} {x y z : ℕ → B} :
    LocalLE h p x (bitsMeet y z) ↔ LocalLE h p x y ∧ LocalLE h p x z := by
  unfold LocalLE
  rw [liveLE_meet_right_r235,le_inf_iff]

theorem LocalLE.join_left_r236 {h : Bool} {p : B} {x y z : ℕ → B} :
    LocalLE h p (bitsJoin x y) z ↔ LocalLE h p x z ∧ LocalLE h p y z := by
  unfold LocalLE
  rw [liveLE_join_left_r235,le_inf_iff]

theorem LocalLE.bot_r236 (h : Bool) (p : B) (x : ℕ → B) :
    LocalLE h p (fun _ => ⊥) x := le_top.trans (liveLE_bot_r235 h x)

theorem LocalLE.top_r236 (h : Bool) (p : B) (x : ℕ → B) :
    LocalLE h p x (fun _ => ⊤) := le_top.trans (liveLE_top_r235 h x)

structure SelectedQuotientIso (B : Type) [NontrivialCompleteBooleanAlgebra B] (p : B) where
  toName : (ℕ → B) → ℕ → B
  invName : (ℕ → B) → ℕ → B
  order : ∀ x y, LocalLE false p x y ↔ LocalLE true p (toName x) (toName y)
  inv_ord : ∀ x, LocalEq false p x (invName (toName x))
  inv_har : ∀ y, LocalEq true p y (toName (invName y))

theorem liveLE_topFromBitEq_r236 {h g : Bool} {p : B} {x y z : ℕ → B}
    (he : p ≤ bitEq (liveLE h x y) (liveLE g z z)) : LocalLE h p x y := by
  have hTop : liveLE g z z = (⊤ : B) := top_unique (nameOrderValue_refl_r229 g (realBitsName z))
  rw [hTop] at he
  have hh := (le_bitEq_iff_r126 p (liveLE h x y) ⊤).mp he
  rw [inf_top_eq] at hh
  exact hh.ge.trans inf_le_right

theorem actualGraph_has_selectedIso_r236 (p : B) (G : bSet B)
    (hG : p ≤ graphPairsOnlyValue G ⊓ (graphTotalSideValue G false ⊓
      (graphTotalSideValue G true ⊓ actualPreserveReflectValue G))) :
    Nonempty (SelectedQuotientIso B p) := by
  obtain ⟨F,R,hF,hR,hOrder⟩ := isoValue_has_two_namedSelections_r214 p G hG
  have hP : p ≤ actualPreserveReflectValue G :=
    hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  refine ⟨⟨F,R,?_,?_,?_⟩⟩
  · intro x y
    have hEq : p ⊓ liveLE false x y = p ⊓ liveLE true (F x) (F y) :=
      (le_bitEq_iff_r126 p _ _).mp (hOrder x y)
    constructor
    · intro h
      exact ((le_inf le_rfl h).trans_eq hEq).trans inf_le_right
    · intro h
      exact ((le_inf le_rfl h).trans_eq hEq.symm).trans inf_le_right
  · intro x
    have h := actualIso_selected_inverseOrd_r229 p G F R hP hF hR x
    exact ⟨h.trans inf_le_left,h.trans inf_le_right⟩
  · intro y
    have h0 : p ≤ graphPairBits G false (R y) y := hR y
    have h1 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) y (F (R y)) h0 (hF (R y))
    have h2 := graph_orderOnSelectedNames_r214 G p hP (R y) (R y) (F (R y)) y (hF (R y)) h0
    have symm (a b : B) : bitEq a b = bitEq b a := inf_comm _ _
    exact ⟨liveLE_topFromBitEq_r236 (h := true) (g := false) (x := y) (y := F (R y)) (z := R y)
        (h1.trans_eq (symm _ _)),
      liveLE_topFromBitEq_r236 (h := true) (g := false) (x := F (R y)) (y := y) (z := R y)
        (h2.trans_eq (symm _ _))⟩

end SetLanguage
end JSP000933
