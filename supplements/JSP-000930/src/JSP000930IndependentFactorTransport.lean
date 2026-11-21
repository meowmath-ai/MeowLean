import JSP000930ActualIndependentTwoStep

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen
open JSP000933.MarkedForcing JSP000933.BooleanCompletion

theorem valuedPoset_ext_values {B N : Type} [CompleteBooleanAlgebra B]
    (P Q : ValuedPoset B N)
    (hV : P.valid = Q.valid) (hR : P.refines = Q.refines) (hW : P.weakest = Q.weakest) : P = Q := by
  cases P with
  | mk pv pr _ _ _ pw _ _ =>
    cases Q with
    | mk qv qr _ _ _ qw _ _ =>
      change pv = qv at hV
      change pr = qr at hR
      change pw = qw at hW
      subst qv
      subst qr
      subst qw
      rfl

variable {B C N M J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem change_supportedSymbolic (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) :
    changeValuedBase F (supportedSymbolicQ site H A) =
      supportedSymbolicQ (fun j => (site j).map F) (fun j n => (H j n).map F) A := by
  apply valuedPoset_ext_values
  · funext p
    exact symbolicLabel_partial_map F site H _ _ (fun j hj => rfl) (fun j hj n => rfl) p.val p.2
  · funext p q
    exact symbolicLabel_refines_partial_map F site H _ _ (fun j hj => rfl) (fun j hj n => rfl)
      p.val q.val p.2 q.2
  · rfl

theorem change_valuedCohen (F : CompleteValueMap B C) (X : Type) :
    changeValuedBase F (valuedCohen B X) = valuedCohen C X := by
  apply valuedPoset_ext_values
  · funext p
    exact F.map_top
  · funext p q
    classical
    by_cases h : p≤q
    · simpa only [changeValuedBase,valuedCohen,ite_eq_left h] using F.map_top
    · simpa only [changeValuedBase,valuedCohen,ite_eq_right h] using F.map_bot
  · rfl

def pairSwapCondition (P : ValuedPoset B N) (Q : ValuedPoset B M) :
    TotalCondition (valuedPair P Q) ≃o TotalCondition (valuedPair Q P) where
  toFun p := ⟨p.mask,p.trace.swap,p.nonzero,le_inf (p.valid.trans inf_le_right) (p.valid.trans inf_le_left)⟩
  invFun p := ⟨p.mask,p.trace.swap,p.nonzero,le_inf (p.valid.trans inf_le_right) (p.valid.trans inf_le_left)⟩
  left_inv := by rintro ⟨b,⟨p,q⟩,hb,hV⟩; rfl
  right_inv := by rintro ⟨b,⟨q,p⟩,hb,hV⟩; rfl
  map_rel_iff' := by
    intro p q
    change (p.mask≤q.mask ∧ p.mask≤Q.refines p.trace.2 q.trace.2 ⊓ P.refines p.trace.1 q.trace.1) ↔
      (p.mask≤q.mask ∧ p.mask≤P.refines p.trace.1 q.trace.1 ⊓ Q.refines p.trace.2 q.trace.2)
    rw [inf_comm (Q.refines p.trace.2 q.trace.2)]

end JSP000930.Negative
