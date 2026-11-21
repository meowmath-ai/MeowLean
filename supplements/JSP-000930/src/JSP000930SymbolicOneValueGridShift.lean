import JSP000930SymbolicOneValueGround
import JSP000930SymbolicDenominatorMargin

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 450000 in
theorem symbolic_named_one_value_grid_shift (p : SymbolicTrace J) (i : PinNumber p)
    (u v : SymbolIndex p → ComplexBits B) (m : B) {R : ℕ} (g : RatGrid R)
    (L η r : ℚ) (hL : 1 ≤ L) (hR : (R : ℚ) ≤ L) (hη : 0 ≤ η) (hr : 0 < r)
    (hu : ∀ a,(u a).CutOn m) (hv : ∀ a,(v a).CutOn m)
    (huA : ∀ j a,a ∈ symbolicOtherSites p j → m ≤ ((u (.inl j)).name =ᴮ (u a).name)ᶜ)
    (hvA : ∀ j a,a ∈ symbolicOtherSites p j → m ≤ ((v (.inl j)).name =ᴮ (v a).name)ᶜ)
    (hSite : ∀ j : PinNumber p,u (.inl j) = v (.inl j))
    (hVal : ∀ j : PinNumber p,j ≠ i → u (.inr j) = v (.inr j))
    (hNB : ∀ j : PinNumber p,m ≤ distanceLe (v (.inl j)) (ComplexBits.checked (0 : ℂ)) L)
    (hClose : m ≤ distanceLe (v (.inr i)) (u (.inr i)) η)
    (hMargin : SymbolicMargin p v m r) :
    m ≤ distanceLe
      (mixedPolynomialEval ((symbolicCoefficients p).map (Expr.eval v))
        (ComplexBits.checked (gridPoint g)))
      (mixedPolynomialEval ((symbolicCoefficients p).map (Expr.eval u))
        (ComplexBits.checked (gridPoint g)))
      (η/r*(L+L)^p.pins.length) := by
  let W := SymbolIndex p × Bool
  let a₀ : SymbolIndex p → W := fun j => (j,false)
  let a₁ : SymbolIndex p → W := fun j => (j,true)
  let t : W → ComplexBits B := fun j => if j.2 then v j.1 else u j.1
  have hUL : t ∘ a₀ = u := rfl
  have hVR : t ∘ a₁ = v := rfl
  haveI : Nonempty W := ⟨(.inl i,false)⟩
  have ht : ∀ j,(t j).CutOn m := by
    rintro ⟨j,k⟩
    cases k
    · exact hu j
    · exact hv j
  let z : Expr (SymbolIndex p) := .num g.1.1 g.1.2
  let f := atExpr (symbolicCoefficients p) z
  let d := symbolicDenominator p i
  let A := f.rename a₁
  let E := f.rename a₀
  let D := d.rename a₁
  have hZ (b : SymbolIndex p → ComplexBits B) : z.Safe b m := by
    intro x hx
    exact (List.not_mem_nil hx).elim
  have hA : A.Safe t m := Expr.safe_rename a₁ t f m
    (atExpr_safe (symbolicCoefficients_safe p m v hv hvA) (hZ v))
  have hE : E.Safe t m := Expr.safe_rename a₀ t f m
    (atExpr_safe (symbolicCoefficients_safe p m u hu huA) (hZ u))
  have hD : D.Safe t m := by
    apply Expr.safe_rename a₁ t d m
    apply atExpr_safe (symbolicVanish_safe p v m i)
    intro x hx
    exact (List.not_mem_nil hx).elim
  suffices hh : m ≤ distanceLe (A.eval t) (E.eval t) (η/r*(L+L)^p.pins.length) by
    simpa only [A,E,Expr.eval_rename,hUL,hVR,f,atExpr_eval,z,Expr.eval,gridPoint] using hh
  apply expr_distance_forced_with_aux t m A E [D] _ ht hA hE
    (fun x hx => (List.mem_singleton.mp hx).symm ▸ hD)
  intro q w hq hnz hqm hTr hAux
  let u₀ := w ∘ a₀
  let v₀ := w ∘ a₁
  have hSame (j : SymbolIndex p) (heq : u j = v j) : u₀ j = v₀ j := by
    have hc : m ≤ (u j).name =ᴮ (v j).name := by
      rw [heq,bSet.bv_eq_refl]
      exact le_top
    exact trace_complex_eq hq hnz hqm (hTr (a₀ j)) (hTr (a₁ j)) hc
  have hZ' : z.evalGround u₀ = z.evalGround v₀ := rfl
  have hFormula := symbolic_ground_one_value_shift p i z u₀ v₀ hZ'
    (fun j => hSame (.inl j) (hSite j)) (fun j hj => hSame (.inr j) (hVal j hj))
  have hL' : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hη' : 0 ≤ (η : ℝ) := by exact_mod_cast hη
  have hshift : ‖v₀ (.inr i) - u₀ (.inr i)‖ ≤ (η : ℝ) := by
    have hi := trace_distanceLe hq hnz hqm (hv (.inr i)) (hu (.inr i))
      (hTr (a₁ (.inr i))) (hTr (a₀ (.inr i))) hη hClose
    simpa only [dist_eq_norm,v₀,u₀,Function.comp_apply] using hi
  have hLZ : ‖z.evalGround v₀‖ ≤ (L : ℝ) :=
    (gridPoint_norm_le g).trans (by exact_mod_cast hR)
  obtain ⟨b,hb,hB⟩ := hMargin i
  have hDb : m ≤ (D.eval t).normSq b := by
    rw [show D.eval t = d.eval v from Expr.eval_rename a₁ t d]
    exact hB
  have hDT := hAux D List.mem_cons_self
  have hDbOrd := trace_forcedMember_le hq hnz
    (hDT.normSq hq hqm (D.eval_cutOn t m ht hD)) b ⟨0,(hqm 0).trans hDb⟩
  have hrB : (r : ℝ)^2 ≤ (b.value : ℝ) := by exact_mod_cast hb
  have hDbSq : (r : ℝ)^2 ≤ ‖d.evalGround v₀‖^2 := by
    have hh := hrB.trans hDbOrd
    simpa only [D,Expr.evalGround_rename,Complex.normSq_eq_norm_sq,v₀] using hh
  have hd : (r : ℝ) ≤ ‖d.evalGround v₀‖ := by
    by_contra hc
    have hh := lt_of_not_ge hc
    nlinarith [mul_pos (sub_pos.mpr hh)
      (add_pos_of_pos_of_nonneg hr' (norm_nonneg (d.evalGround v₀)))]
  have hProd := symbolic_anchor_product_bound p i z v₀ (L : ℝ) hL' hLZ (by
    intro j
    have hj := trace_distanceLe hq hnz hqm (hv (.inl j)) (ComplexBits.checked_cutOn 0 m)
      (hTr (a₁ (.inl j))) (checked_complex_traces q 0) (zero_le_one.trans hL) (hNB j)
    simpa only [dist_zero_right,v₀,Function.comp_apply] using hj)
  rw [dist_eq_norm,show A.evalGround w = (atExpr (symbolicCoefficients p) z).evalGround v₀
      from Expr.evalGround_rename a₁ w f,
    show E.evalGround w = (atExpr (symbolicCoefficients p) z).evalGround u₀
      from Expr.evalGround_rename a₀ w f,hFormula,Complex.norm_mul,Complex.norm_div]
  have hDen : ((symbolicOtherSites p i).map (fun s => v₀ (.inl i) - v₀ s)).prod =
      d.evalGround v₀ := (symbolicVanish_ground p i (.atom (.inl i)) v₀).symm
  rw [hDen]
  push_cast
  refine mul_le_mul ?_ hProd (norm_nonneg _) (div_nonneg hη' hr'.le)
  apply (div_le_div_iff₀ (hr'.trans_le hd) hr').mpr
  exact (mul_le_mul_of_nonneg_right hshift hr'.le).trans (mul_le_mul_of_nonneg_left hd hη')

end JSP000930.Negative
