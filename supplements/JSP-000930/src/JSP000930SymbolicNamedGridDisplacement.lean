import JSP000930SymbolicDenominatorMargin

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem safe_atom_p94 (p : SymbolicTrace J)
    (u : SymbolIndex p → ComplexBits B) (m : B) (i : SymbolIndex p) :
    (Expr.atom i).Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

theorem symbolic_named_grid_displacement (p : SymbolicTrace J)
    (u : SymbolIndex p → ComplexBits B) (m : B)
    {R : ℕ} (g : RatGrid R) (L η r : ℚ)
    (hL : 1 ≤ L) (hR : (R : ℚ) ≤ L) (hη : 0 ≤ η) (hr : 0 < r)
    (hu : ∀ a,(u a).CutOn m)
    (hApart : ∀ i a,a ∈ symbolicOtherSites p i → m ≤ ((u (.inl i)).name =ᴮ (u a).name)ᶜ)
    (hS : ∀ i : PinNumber p,m ≤ distanceLe (u (.inl i)) (ComplexBits.checked (0 : ℂ)) L)
    (hNear : ∀ i : PinNumber p,m ≤ distanceLe (u (.inr i)) ((symbolicAtPinSeed p i).eval u) η)
    (hMargin : SymbolicMargin p u m r) :
    m ≤ distanceLe
      (mixedPolynomialEval ((symbolicCoefficients p).map (Expr.eval u))
        (ComplexBits.checked (gridPoint g)))
      (mixedPolynomialEval (p.seed.map (fun a => ComplexBits.checked (gaussianRat a)))
        (ComplexBits.checked (gridPoint g)))
      ((p.pins.length : ℚ)*(η/r*(L+L)^p.pins.length)) := by
  classical
  let z : Expr (SymbolIndex p) := .num g.1.1 g.1.2
  let a := atExpr (symbolicCoefficients p) z
  let b := atExpr (seedExpr p) z
  let e := (p.pins.length : ℚ)*(η/r*(L+L)^p.pins.length)
  have hZ : z.Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hB : b.Safe u m := atExpr_safe (seedExpr_safe p u m) hZ
  have hA : a.Safe u m := atExpr_safe (symbolicCoefficients_safe p m u hu hApart) hZ
  suffices h : m ≤ distanceLe (a.eval u) (b.eval u) e by
    simpa only [a,b,e,atExpr_eval,seedExpr,mixedPolynomialEval_map_seed,z,Expr.eval,gridPoint]
      using h
  by_cases hZero : p.pins.length = 0
  · have hI : symbolicIndices p = [] :=
      List.length_eq_zero_iff.mp (by simpa only [symbolicIndices,List.length_ofFn] using hZero)
    have hEq : symbolicCoefficients p = seedExpr p := by
      unfold symbolicCoefficients
      rw [hI]
      cases seedExpr p <;> rfl
    have heq : a = b := congrArg (fun q => atExpr q z) hEq
    rw [heq]
    exact distanceLe_self (b.eval_cutOn u m hu hB) e
  haveI : Nonempty (SymbolIndex p) := ⟨.inl ⟨0,Nat.pos_of_ne_zero hZero⟩⟩
  let aux := (symbolicIndices p).map (symbolicAtPinSeed p) ++
    (symbolicIndices p).map (symbolicDenominator p)
  have hAux (x : Expr (SymbolIndex p)) (hx : x ∈ aux) : x.Safe u m := by
    rcases List.mem_append.mp hx with h|h
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      exact atExpr_safe (seedExpr_safe p u m) (safe_atom_p94 p u m (.inl i))
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      exact atExpr_safe (symbolicVanish_safe p u m i) (safe_atom_p94 p u m (.inl i))
  apply expr_distance_forced_with_aux u m a b aux e hu hA hB hAux
  intro q w hq hnz hqm ht hTr
  have hL' : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hR' : (R : ℝ) ≤ (L : ℝ) := by exact_mod_cast hR
  have hη' : 0 ≤ (η : ℝ) := by exact_mod_cast hη
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hG : ‖z.evalGround w‖ ≤ (L : ℝ) := (gridPoint_norm_le g).trans hR'
  have hNamedS (i : PinNumber p) : ‖w (.inl i)‖ ≤ (L : ℝ) := by
    have hx := trace_distanceLe hq hnz hqm (hu (.inl i)) (ComplexBits.checked_cutOn 0 m)
      (ht (.inl i)) (checked_complex_traces q 0) (zero_le_one.trans hL) (hS i)
    simpa only [dist_zero_right] using hx
  have hNamedNear (i : PinNumber p) :
      dist (w (.inr i)) ((symbolicAtPinSeed p i).evalGround w) ≤ (η : ℝ) := by
    have hi : symbolicAtPinSeed p i ∈ aux := List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨i,mem_symbolicIndices p i,rfl⟩))
    exact trace_distanceLe hq hnz hqm (hu (.inr i))
      ((symbolicAtPinSeed p i).eval_cutOn u m hu (hAux _ hi)) (ht (.inr i))
      (hTr _ hi) hη (hNear i)
  have hNamedDen (i : PinNumber p) :
      (r : ℝ) ≤ ‖(symbolicDenominator p i).evalGround w‖ := by
    let d := symbolicDenominator p i
    have hi : d ∈ aux := List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨i,mem_symbolicIndices p i,rfl⟩))
    obtain ⟨c,hc,hMem⟩ := hMargin i
    have hc' : (r : ℝ)^2 ≤ (c.value : ℝ) := by exact_mod_cast hc
    have hdValid := d.eval_cutOn u m hu (hAux _ hi)
    have hSq := trace_forcedMember_le hq hnz ((hTr d hi).normSq hq hqm hdValid)
      c ⟨0,(hqm 0).trans hMem⟩
    have hn : (r : ℝ)^2 ≤ ‖d.evalGround w‖^2 :=
      hc'.trans (by simpa only [Complex.normSq_eq_norm_sq] using hSq)
    by_contra h
    have hh := lt_of_not_ge h
    nlinarith [mul_pos (sub_pos.mpr hh)
      (add_pos_of_pos_of_nonneg hr' (norm_nonneg (d.evalGround w)))]
  have hf := symbolic_ground_seed_displacement p z w (L : ℝ) (η : ℝ) (r : ℝ)
    hL' hη' hr' hG hNamedS hNamedNear hNamedDen
  simpa only [a,b,e,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast] using hf

end JSP000930.Negative
