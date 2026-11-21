import JSP000930NamedVanishingNonzero

open Lattice
open scoped Flypitch bSet BigOperators

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

namespace ExprPoly

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B] [Countable V] [Nonempty V]

theorem forced_eq_of_apart_sites (u : V → ComplexBits B) (z : V) (old : List V)
    (m : B) (a b : Expr V) (hu : ∀ i, (u i).CutOn m)
    (ha : a.Safe u m) (hb : b.Safe u m)
    (hApart : ∀ i ∈ old, m ≤ ((u z).name =ᴮ (u i).name)ᶜ)
    (hLaw : ∀ w : V → ℂ, (∀ i ∈ old, w z ≠ w i) → a.evalGround w = b.evalGround w) :
    m ≤ (a.eval u).name =ᴮ (b.eval u).name := by
  by_contra h
  let eq := ((a.eval u).name =ᴮ (b.eval u).name)
  let bad := m ⊓ eqᶜ
  have hn : bad ≠ ⊥ := fun he =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  have hB : bad ≤ m := inf_le_left
  have huB : ∀ i, (u i).CutOn bad := fun i =>
    ⟨properCutOn_mono hB (hu i).1, properCutOn_mono hB (hu i).2⟩
  obtain ⟨s,hs,hsB,hS⟩ := exists_fixed_apart_sites u z old bad hn huB
    (fun i hi => hB.trans (hApart i hi))
  have hsM : s ≤ m := hsB.trans hB
  have huS : ∀ i, (u i).CutOn s := fun i =>
    ⟨properCutOn_mono hsM (hu i).1, properCutOn_mono hsM (hu i).2⟩
  have hA : s ≤ eq := expr_eq_forced u s a b huS (Expr.safe_mono ha hsM) (Expr.safe_mono hb hsM)
    (fun p w hp hnz hps ht => hLaw w (hS p w hp hnz hps ht))
  exact hs (disjoint_compl_right.out _ hA (hsB.trans inf_le_right))

theorem scalar_factors_ne_zero (w : V → ℂ) (z : V) (old : List V)
    (h : ∀ a ∈ old, w z ≠ w a) :
    (old.map (fun a => w z - w a)).prod ≠ 0 := by
  induction old with
  | nil => simp
  | cons a old ih =>
    simp only [List.map_cons,List.prod_cons]
    exact mul_ne_zero (sub_ne_zero.mpr (h a List.mem_cons_self))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem scalar_factors_zero_of_mem (w : V → ℂ) (z : V) (old : List V) (hz : z ∈ old) :
    (old.map (fun a => w z - w a)).prod = 0 := by
  induction old with
  | nil => exact (List.not_mem_nil hz).elim
  | cons a old ih =>
    rcases List.mem_cons.mp hz with he | h
    · subst a
      simp only [List.map_cons,List.prod_cons,sub_self,zero_mul]
    · simp only [List.map_cons,List.prod_cons,ih h,mul_zero]

theorem named_one_pin_exact (u : V → ComplexBits B) (m : B)
    (p : Poly V) (old : List V) (z y : V)
    (hu : ∀ i, (u i).CutOn m) (hp : CoeffSafe u m p)
    (hApart : ∀ i ∈ old, m ≤ ((u z).name =ᴮ (u i).name)ᶜ) :
    ∃ q : List (ComplexBits B),
      q = (displacement p (old.map Expr.atom) (.atom z) (.atom y)).map (Expr.eval u) ∧
      (∀ c ∈ q, c.CutOn m) ∧
      (m ≤ (mixedPolynomialEval q (u z)).name =ᴮ (u y).name) ∧
      ∀ i ∈ old, m ≤ (mixedPolynomialEval q (u i)).name =ᴮ
        (mixedPolynomialEval (p.map (Expr.eval u)) (u i)).name := by
  let q := displacement p (old.map Expr.atom) (.atom z) (.atom y)
  have hs (i : V) : (Expr.atom i).Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hOld : CoeffSafe u m (old.map Expr.atom) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact hs i
  have hD := named_vanishing_positive u z old m hu hApart
  have hq : CoeffSafe u m q := coeffSafe_displacement hp hOld (hs z) (hs y) hD
  refine ⟨q.map (Expr.eval u), rfl, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact a.eval_cutOn u m hu (hq a ha)
  · have h := forced_eq_of_apart_sites u z old m (atExpr q (.atom z)) (.atom y) hu
      (atExpr_safe hq (hs z)) (hs y) hApart (by
        intro w hsep
        have hNZ := scalar_factors_ne_zero w z old hsep
        change (atExpr (displacement p (old.map Expr.atom) (.atom z) (.atom y))
          (.atom z)).evalGround w = w y
        rw [atExpr_displacement]
        simp only [List.map_map, Function.comp_apply, Expr.evalGround]
        change _ + (_ / (old.map (fun a => w z - w a)).prod) *
          (old.map (fun a => w z - w a)).prod = _
        rw [div_mul_cancel₀ _ hNZ]
        ring)
    simpa only [atExpr_eval,Expr.eval] using h
  · intro i hi
    have h := expr_eq_forced u m (atExpr q (.atom i)) (atExpr p (.atom i)) hu
      (atExpr_safe hq (hs i)) (atExpr_safe hp (hs i)) (by
        intro t w ht hnz htm hw
        have h0 := scalar_factors_zero_of_mem w i old hi
        change (atExpr (displacement p (old.map Expr.atom) (.atom z) (.atom y))
          (.atom i)).evalGround w = _
        rw [atExpr_displacement]
        simp only [List.map_map, Function.comp_apply, Expr.evalGround]
        change _ + (_ / _) * (old.map (fun a => w i - w a)).prod = _
        rw [h0,mul_zero,add_zero])
    simpa only [atExpr_eval,Expr.eval] using h

end ExprPoly

end JSP000930.Negative
