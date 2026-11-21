import JSP000930ExpressionCoefficientSafety

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_fixed_apart_sites (u : V → ComplexBits B) (z : V) (old : List V)
    (m : B) (hm : m ≠ ⊥) (hu : ∀ i, (u i).CutOn m)
    (hApart : ∀ a ∈ old, m ≤ ((u z).name =ᴮ (u a).name)ᶜ) :
    ∃ s : B, s ≠ ⊥ ∧ s ≤ m ∧
      ∀ (p : ℕ → B) (w : V → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
        (∀ n,p n ≤ s) → (∀ i, ComplexDecisionTrace p (u i) (w i)) →
        ∀ a ∈ old, w z ≠ w a := by
  induction old generalizing m with
  | nil =>
    refine ⟨m,hm,le_rfl,?_⟩
    intro p w hp hn hs ht a ha
    exact (List.not_mem_nil ha).elim
  | cons a old ih =>
    have hNe : ¬ m ≤ (u z).name =ᴮ (u a).name := fun he =>
      hm (disjoint_compl_right.out _ he (hApart a List.mem_cons_self))
    obtain ⟨k,hk,hkm,hSep⟩ := complex_eq_fail_survives (hu z) (hu a) hNe
    have huK : ∀ i, (u i).CutOn k := fun i =>
      ⟨properCutOn_mono hkm (hu i).1, properCutOn_mono hkm (hu i).2⟩
    obtain ⟨s,hs,hsk,hS⟩ := ih k hk huK
      (fun b hb => hkm.trans (hApart b (List.mem_cons_of_mem _ hb)))
    refine ⟨s,hs,hsk.trans hkm,?_⟩
    intro p w hp hn hps ht b hb
    rcases List.mem_cons.mp hb with he | hb
    · exact he.symm ▸ (hSep hp hn (fun n => (hps n).trans hsk) (ht z) (ht a))
    · exact hS p w hp hn hps ht b hb

theorem named_vanishing_positive [Countable V] [Nonempty V]
    (u : V → ComplexBits B) (z : V) (old : List V) (m : B)
    (hu : ∀ i, (u i).CutOn m)
    (hApart : ∀ a ∈ old, m ≤ ((u z).name =ᴮ (u a).name)ᶜ) :
    m ≤ positiveCutValue ((ExprPoly.atExpr (ExprPoly.vanishing (old.map Expr.atom))
      (Expr.atom z)).eval u).normSq := by
  let e := ExprPoly.atExpr (ExprPoly.vanishing (old.map Expr.atom)) (Expr.atom z)
  change m ≤ positiveCutValue (e.eval u).normSq
  have hSafe : ExprPoly.CoeffSafe u m (old.map Expr.atom) := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hz : (Expr.atom z).Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hE : e.Safe u m := ExprPoly.atExpr_safe (ExprPoly.coeffSafe_vanishing hSafe) hz
  by_contra h
  let bad := m ⊓ (positiveCutValue (e.eval u).normSq)ᶜ
  have hbad : bad ≠ ⊥ := fun he =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  have hbM : bad ≤ m := inf_le_left
  have huB : ∀ i, (u i).CutOn bad := fun i =>
    ⟨properCutOn_mono hbM (hu i).1,properCutOn_mono hbM (hu i).2⟩
  obtain ⟨s,hs,hsB,hSep⟩ := exists_fixed_apart_sites u z old bad hbad huB
    (fun a ha => hbM.trans (hApart a ha))
  have hsM := hsB.trans hbM
  have huS : ∀ i, (u i).CutOn s := fun i =>
    ⟨properCutOn_mono hsM (hu i).1,properCutOn_mono hsM (hu i).2⟩
  have hList : ∀ d ∈ [e], d.Safe u s := by
    intro d hd
    have heq : d = e := List.mem_singleton.mp hd
    subst d
    exact Expr.safe_mono hE hsM
  obtain ⟨p,w,hp,hnz,hps,ht,hTr⟩ := exists_expr_decision_completion u s hs huS [e] hList
  have hTrE := hTr e List.mem_cons_self
  have hfactors : ∀ a ∈ old, w z - w a ≠ 0 :=
    fun a ha => sub_ne_zero.mpr (hSep p w hp hnz hps ht a ha)
  have hVal : e.evalGround w ≠ 0 := by
    change (ExprPoly.atExpr (ExprPoly.vanishing (old.map Expr.atom))
      (Expr.atom z)).evalGround w ≠ 0
    rw [ExprPoly.atExpr_vanishing]
    have hProd (l : List V) (hL : ∀ a ∈ l, w z - w a ≠ 0) :
        (l.map (fun a => w z - w a)).prod ≠ 0 := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_ne_zero (hL a List.mem_cons_self)
          (ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)))
    simp only [List.map_map]
    exact hProd old hfactors
  have hnorm := hTrE.normSq hp hps (e.eval_cutOn u s huS (Expr.safe_mono hE hsM))
  have hN : 0 < Complex.normSq (e.evalGround w) := Complex.normSq_pos.mpr hVal
  obtain ⟨x,hx,hx'⟩ := exists_rat_btwn hN
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective x
  have hq₀ : 0 < q.value := by rw [hq]; exact_mod_cast hx
  have hq₁ : (q.value : ℝ) < Complex.normSq (e.evalGround w) := by rwa [hq]
  obtain ⟨n,hn⟩ := hnorm.below q hq₁
  have hMark : p n ≤ positiveCutValue (e.eval u).normSq := hn.trans (le_iSup (fun a : {r : RatPresentation // 0 < r.value} => (e.eval u).normSq a.val) ⟨q,hq₀⟩)
  exact hnz n (disjoint_compl_right.out _ hMark ((hps n).trans (hsB.trans inf_le_right)))

end JSP000930.Negative
