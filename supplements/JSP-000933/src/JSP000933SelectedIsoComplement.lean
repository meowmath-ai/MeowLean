import JSP000933SelectedIsoLatticePreservation

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameBudgetValue_disjoint_r238 (h : Bool) (x y : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName x) (realBitsName (bitsComplement y)) k n =
      nameBudgetValue h (realBitsName (bitsMeet x y)) (realBitsName (fun _ => ⊥)) k n := by
  let U : BudgetExpr (Fin 2) := ⟨h,.var 0,.neg (.var 1),k⟩
  let W : BudgetExpr (Fin 2) := ⟨h,.meet (.var 0) (.var 1),.const false,k⟩
  let A (i : Fin 2) := realBitsName (twoBitProfiles x y i)
  have hG (a : Fin 2 → Set ℕ) : U.groundHolds a n ↔ W.groundHolds a n := by
    classical
    have he : U.left.groundSet a \ U.right.groundSet a = W.left.groundSet a \ W.right.groundSet a := by
      ext i
      simp [U,W,SetBitExpr.groundSet,SetBitExpr.evalProp]
    unfold BudgetExpr.groundHolds
    rw [groundBudgetHolds_weighted_r232,groundBudgetHolds_weighted_r232]
    exact Iff.of_eq (congrArg (fun D => k*groundBudgetMass h n D ≤ groundBudgetDenom h n) he)
  have hv := le_antisymm
    (finite_budget_unary_r233 U W A n (fun a => (hG a).mp))
    (finite_budget_unary_r233 W U A n (fun a => (hG a).mpr))
  simp [U,W,A,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.evalB,twoBitProfiles,
    truthBit,membershipBits_realBitsName_r128] at hv
  exact hv

theorem liveLE_disjoint_r238 (h : Bool) (x y : ℕ → B) :
    liveLE h x (bitsComplement y) = liveLE h (bitsMeet x y) (fun _ => ⊥) := by
  unfold liveLE nameOrderValue
  exact congrArg mixedEventualBudgetValue (funext (fun k => funext (fun n =>
    nameBudgetValue_disjoint_r238 h x y k n)))

theorem bitsMeet_comm_r238 (x y : ℕ → B) : bitsMeet x y = bitsMeet y x := by
  funext n
  exact inf_comm _ _

theorem bitsMeet_compl_r238 (x : ℕ → B) :
    bitsMeet x (bitsComplement x) = fun _ => ⊥ := by
  funext n
  exact inf_compl_eq_bot'

theorem bitsJoin_compl_r238 (x : ℕ → B) :
    bitsJoin x (bitsComplement x) = fun _ => ⊤ := by
  funext n
  exact sup_compl_eq_top

theorem bitsCompl_join_r238 (x y : ℕ → B) :
    bitsComplement (bitsJoin x y) = bitsMeet (bitsComplement x) (bitsComplement y) := by
  rw [bitsJoin_deMorgan_r234,bitsComplement_compl_r234]

theorem bitsCompl_top_r238 :
    bitsComplement (fun _ : ℕ => (⊤ : B)) = fun _ => ⊥ := by
  funext n
  exact compl_top

theorem LocalEq.complement_unique_r238 {h : Bool} {p : B} {a b : ℕ → B}
    (hM : LocalLE h p (bitsMeet a b) (fun _ => ⊥))
    (hJ : LocalLE h p (fun _ => ⊤) (bitsJoin a b)) :
    LocalEq h p b (bitsComplement a) := by
  constructor
  · unfold LocalLE
    rw [liveLE_disjoint_r238,bitsMeet_comm_r238 b a]
    exact hM
  · have h : LocalLE h p (bitsComplement (bitsJoin a b)) (fun _ => ⊥) := by
      unfold LocalLE
      rw [← bitsCompl_top_r238,liveLE_compl_reverse_r235]
      exact hJ
    unfold LocalLE
    rw [← bitsComplement_compl_r234 b,liveLE_disjoint_r238,← bitsCompl_join_r238]
    exact h

theorem SelectedQuotientIso.mapCompl_r238 {p : B} (F : SelectedQuotientIso B p) (x : ℕ → B) :
    LocalEq true p (F.toName (bitsComplement x)) (bitsComplement (F.toName x)) := by
  have hm := (F.mapMeet_r237 x (bitsComplement x)).symm_r236
  have hj := (F.mapJoin_r237 x (bitsComplement x)).symm_r236
  rw [bitsMeet_compl_r238] at hm
  rw [bitsJoin_compl_r238] at hj
  exact LocalEq.complement_unique_r238 (hm.trans_r236 F.mapBot_r237).1 (hj.trans_r236 F.mapTop_r237).2

end SetLanguage
end JSP000933
