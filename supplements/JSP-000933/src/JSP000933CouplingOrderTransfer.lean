import JSP000933ActualGenericCoupling

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace PositiveForcing

open CantorCodes BooleanNames BooleanCompletion Erdos1123

noncomputable def crispTruth (B : Type) [CompleteBooleanAlgebra B] (p : Prop) : B := by
  classical
  exact if p then ⊤ else ⊥

theorem crispTruth_propext_r188 {B : Type} [CompleteBooleanAlgebra B] {p q : Prop}
    (h : p ↔ q) : crispTruth B p = crispTruth B q :=
  congrArg (crispTruth B) (propext h)

section Valuation

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def BExtTwo (E : bSet B → bSet B → B) : Prop :=
  ∀ (p : B) (a a' b b' : bSet B), p ≤ a =ᴮ a' → p ≤ b =ᴮ b' →
    p ⊓ E a b = p ⊓ E a' b'

noncomputable def graphOrderValue (G : bSet B) (O H : bSet B → bSet B → B) : B :=
  ⨅ a : bSet B, ⨅ a' : bSet B, ⨅ b : bSet B, ⨅ b' : bSet B,
    imp ((bSet.pair a b ∈ᴮ G) ⊓ (bSet.pair a' b' ∈ᴮ G)) (bitEq (O a a') (H b b'))

end Valuation

variable {W V : WeightSequence ℕ}

theorem generic_graph_orderOfCanonical_arithmetic_r188
    (O H : bSet (CouplingBA W V) → bSet (CouplingBA W V) → CouplingBA W V)
    (hO : BExtTwo O) (hH : BExtTwo H)
    (hOrd : ∀ a b : Set ℕ, O (groundSubsetName _ (fromPositive a)) (groundSubsetName _ (fromPositive b)) =
      crispTruth (CouplingBA W V) (W.IsNull (a \ b)))
    (hHar : ∀ a b : Set ℕ, H (groundSubsetName _ (fromPositive a)) (groundSubsetName _ (fromPositive b)) =
      crispTruth (CouplingBA W V) (V.IsNull (a \ b))) :
    (⊤ : CouplingBA W V) ≤ graphOrderValue (genericCouplingGraph W V) O H := by
  classical
  apply le_iInf
  intro a
  apply le_iInf
  intro a'
  apply le_iInf
  intro b
  apply le_iInf
  intro b'
  rw [← _root_.deduction,top_inf_eq]
  change ((bSet.pair a b ∈ᴮ familyName (genericCouplingPair W V) (pairValue (W := W) (V := V))) ⊓
    (bSet.pair a' b' ∈ᴮ familyName (genericCouplingPair W V) (pairValue (W := W) (V := V)))) ≤ _
  rw [mem_familyName_r70,mem_familyName_r70,iSup_inf_iSup]
  apply iSup_le
  intro rs
  let r := rs.1
  let s := rs.2
  let R := genericCouplingPair W V r
  let S := genericCouplingPair W V s
  let p := (pairValue (W := W) (V := V) r ⊓ (bSet.pair a b =ᴮ R)) ⊓
    (pairValue (W := W) (V := V) s ⊓ (bSet.pair a' b' =ᴮ S))
  change p ≤ bitEq (O a a') (H b b')
  by_cases h : W.IsNull (r.1 \ s.1) ↔ V.IsNull (r.2 \ s.2)
  · have hr : p ≤ bSet.pair a b =ᴮ R := inf_le_left.trans inf_le_right
    have hs : p ≤ bSet.pair a' b' =ᴮ S := inf_le_right.trans inf_le_right
    have hOL := hO p _ _ _ _ (hr.trans bSet.eq_of_eq_pair_left) (hs.trans bSet.eq_of_eq_pair_left)
    have hHR := hH p _ _ _ _ (hr.trans bSet.eq_of_eq_pair_right) (hs.trans bSet.eq_of_eq_pair_right)
    apply (le_bitEq_iff_r126 p _ _).mpr
    refine hOL.trans (Eq.trans ?_ hHR.symm)
    rw [hOrd,hHar,crispTruth_propext_r188 h]
  · exact ((le_inf (show p ≤ pairValue (W := W) (V := V) r from inf_le_left.trans inf_le_left)
      (show p ≤ pairValue (W := W) (V := V) s from inf_le_right.trans inf_le_left)).trans_eq
        (pairValue_disagree_inf_bot_r184 r s h)).trans bot_le

end PositiveForcing
end JSP000933
