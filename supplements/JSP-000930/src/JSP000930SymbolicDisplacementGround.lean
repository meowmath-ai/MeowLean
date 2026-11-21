import JSP000930ExpressionContextRename
import JSP000930NamedDisplacementDiscControl

namespace JSP000930.Negative

open ExprPoly

variable {J : Type}

private theorem one_le_power_normalization {x : ℝ} (h : 1 ≤ x) (n : ℕ) :
    1 ≤ x^n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ x^k * x := mul_le_mul ih h zero_le_one (zero_le_one.trans ih)

private theorem power_mono_exponent_normalization {x : ℝ} (h : 1 ≤ x)
    {a b : ℕ} (hab : a ≤ b) : x^a ≤ x^b := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc
    x^a = x^a * 1 := by ring
    _ ≤ x^a * x^t := mul_le_mul_of_nonneg_left (one_le_power_normalization h t)
      (pow_nonneg (zero_le_one.trans h) a)

private theorem list_sum_norm_bound_normalization {I : Type} (l : List I) (f : I → ℂ)
    (d : ℝ) (h : ∀ i ∈ l,‖f i‖ ≤ d) :
    ‖(l.map f).sum‖ ≤ (l.length : ℝ)*d := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      ‖f i + (l.map f).sum‖ ≤ ‖f i‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ d + (l.length : ℝ)*d := add_le_add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))
      _ = ((l.length : ℝ)+1)*d := by ring

theorem symbolicOtherSites_length_le (p : SymbolicTrace J) (i : PinNumber p) :
    (symbolicOtherSites p i).length ≤ p.pins.length := by
  unfold symbolicOtherSites
  rw [List.length_map]
  apply (List.length_filter_le _ _).trans
  simp only [symbolicIndices,List.length_ofFn,le_rfl]

theorem symbolic_ground_seed_displacement (p : SymbolicTrace J)
    (z : Expr (SymbolIndex p)) (w : SymbolIndex p → ℂ) (L η r : ℝ)
    (hL : 1 ≤ L) (hη : 0 ≤ η) (hr : 0 < r)
    (hZ : ‖z.evalGround w‖ ≤ L)
    (hS : ∀ i : PinNumber p,‖w (.inl i)‖ ≤ L)
    (hNear : ∀ i : PinNumber p,
      dist (w (.inr i)) ((atExpr (seedExpr p) (.atom (.inl i))).evalGround w) ≤ η)
    (hDen : ∀ i : PinNumber p,
      r ≤ ‖(atExpr (symbolicVanish p i) (.atom (.inl i))).evalGround w‖) :
    dist ((atExpr (symbolicCoefficients p) z).evalGround w)
      ((atExpr (seedExpr p) z).evalGround w) ≤
        (p.pins.length : ℝ)*(η/r*(L+L)^p.pins.length) := by
  let c (i : PinNumber p) := (atExpr (symbolicCorrection p i) z).evalGround w
  have hOne : 1 ≤ L+L := by linarith
  have hC (i : PinNumber p) : ‖c i‖ ≤ η/r*(L+L)^p.pins.length := by
    let a := atExpr (seedExpr p) (.atom (.inl i))
    let d := atExpr (symbolicVanish p i) (.atom (.inl i))
    have hD : 0 < ‖d.evalGround w‖ := hr.trans_le (hDen i)
    have hNum : ‖w (.inr i) - a.evalGround w‖ ≤ η := by
      simpa only [dist_eq_norm] using hNear i
    have hDiv : ‖w (.inr i) - a.evalGround w‖ / ‖d.evalGround w‖ ≤ η/r := by
      apply (div_le_div_iff₀ hD hr).mpr
      exact (mul_le_mul_of_nonneg_right hNum hr.le).trans
        (mul_le_mul_of_nonneg_left (hDen i) hη)
    let l := symbolicOtherSites p i
    let u : Option (SymbolIndex p) → ℂ
      | none => z.evalGround w
      | some i => w i
    have hNorms : ∀ s ∈ l.map some, ‖u s‖ ≤ L := by
      intro s hs
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      obtain ⟨j,hj,rfl⟩ := (mem_symbolicOtherSites p i a).mp ha
      exact hS j
    have hProd : ‖(l.map (fun s => z.evalGround w - w s)).prod‖ ≤ (L+L)^p.pins.length := by
      have hp := scalar_anchor_bound u (l.map some) none (zero_le_one.trans hL)
        (zero_le_one.trans hL) hZ hNorms
      simp only [List.map_map,List.length_map,Function.comp_apply,u] at hp
      exact hp.trans (power_mono_exponent_normalization hOne (symbolicOtherSites_length_le p i))
    have hRepr : c i =
        (w (.inr i) - a.evalGround w) / d.evalGround w *
          (l.map (fun s => z.evalGround w - w s)).prod := by
      unfold c d
      rw [symbolicCorrection_ground,symbolicVanish_ground] <;> rfl
    rw [hRepr,Complex.norm_mul,Complex.norm_div]
    exact mul_le_mul hDiv hProd (norm_nonneg _) (div_nonneg hη hr.le)
  rw [symbolicCoefficients_ground,dist_eq_norm]
  have hSub : (atExpr (seedExpr p) z).evalGround w + ((symbolicIndices p).map c).sum -
      (atExpr (seedExpr p) z).evalGround w = ((symbolicIndices p).map c).sum := by abel
  change ‖(atExpr (seedExpr p) z).evalGround w + ((symbolicIndices p).map c).sum -
      (atExpr (seedExpr p) z).evalGround w‖ ≤ _
  rw [hSub]
  simpa only [symbolicIndices,List.length_ofFn] using
    list_sum_norm_bound_normalization (symbolicIndices p) c (η/r*(L+L)^p.pins.length)
      (fun i _ => hC i)

end JSP000930.Negative
