import JSP000930SymbolicPolynomialTrace
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace JSP000930.Negative

open Cardinal

variable {J : Type}

def encodeSymbolicTrace (x : SymbolicTrace J) :
    List (ℚ × ℚ) × List (J × ℕ) × ℕ × ℚ :=
  (x.seed,x.pins,x.radius,x.budget)

theorem encodeSymbolicTrace_injective :
    Function.Injective (encodeSymbolicTrace (J := J)) := by
  intro p q h
  cases p with
  | mk a i r e he hi =>
    cases q with
    | mk b j s f hf hj =>
      have h₁ : a = b := congrArg Prod.fst h
      have h₂ : i = j := congrArg (fun z => z.2.1) h
      have h₃ : r = s := congrArg (fun z => z.2.2.1) h
      have h₄ : e = f := congrArg (fun z => z.2.2.2) h
      subst b
      subst j
      subst s
      subst f
      rfl

theorem symbolicTrace_card_le (κ : Cardinal) (hκ : ℵ₀ ≤ κ)
    (hJ : Cardinal.mk J ≤ κ) : Cardinal.mk (SymbolicTrace J) ≤ κ := by
  have hN : Cardinal.mk ℕ ≤ κ := Cardinal.mk_le_aleph0.trans hκ
  have hQ : Cardinal.mk ℚ ≤ κ := Cardinal.mk_le_aleph0.trans hκ
  have hQQ : Cardinal.mk (ℚ × ℚ) ≤ κ := by
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact Cardinal.mul_le_of_le hκ hQ hQ
  have hJN : Cardinal.mk (J × ℕ) ≤ κ := by
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact Cardinal.mul_le_of_le hκ hJ hN
  have hA : Cardinal.mk (List (ℚ × ℚ)) ≤ κ :=
    (Cardinal.mk_list_le_max _).trans (max_le hκ hQQ)
  have hB : Cardinal.mk (List (J × ℕ)) ≤ κ :=
    (Cardinal.mk_list_le_max _).trans (max_le hκ hJN)
  apply (Cardinal.mk_le_of_injective encodeSymbolicTrace_injective).trans
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hκ hA
    (Cardinal.mul_le_of_le hκ hB (Cardinal.mul_le_of_le hκ hN hQ))

theorem symbolicTrace_countable [Countable J] : Countable (SymbolicTrace J) :=
  Function.Injective.countable encodeSymbolicTrace_injective

end JSP000930.Negative
