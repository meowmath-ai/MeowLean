import JSP000930FiniteMetricLawContext

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

namespace ExprPoly

variable {B V : Type} [NontrivialCompleteBooleanAlgebra B] [Countable V] [Nonempty V]

theorem scalar_anchor_bound (x : V → ℂ) (old : List V) (w : V) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hw : ‖x w‖ ≤ R) (hu : ∀ i ∈ old, ‖x i‖ ≤ L) :
    ‖(old.map (fun i => x w - x i)).prod‖ ≤ (R + L) ^ old.length := by
  induction old with
  | nil => simp
  | cons a old ih =>
    simp only [List.map_cons, List.prod_cons, Complex.norm_mul, List.length_cons, pow_succ]
    have ha : ‖x w - x a‖ ≤ R + L :=
      (norm_sub_le _ _).trans (add_le_add hw (hu _ List.mem_cons_self))
    have hp := ih (fun b hb => hu b (List.mem_cons_of_mem _ hb))
    rw [mul_comm ((R + L) ^ old.length) (R + L)]
    exact mul_le_mul ha hp (norm_nonneg _) (add_nonneg hR hL)

theorem named_displacement_disc_control (u : V → ComplexBits B) (m : B)
    (p : Poly V) (old : List V) (z y w : V) (R L η e r : ℚ)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hη : 0 ≤ η) (hr : 0 < r)
    (hQuant : η * (R + L)^old.length ≤ e * r)
    (hu : ∀ i, (u i).CutOn m) (hp : CoeffSafe u m p)
    (hOld : ∀ i ∈ old, m ≤ distanceLe (u i) (ComplexBits.checked (0 : ℂ)) L)
    (hW : m ≤ distanceLe (u w) (ComplexBits.checked (0 : ℂ)) R)
    (hNear : m ≤ distanceLe (u y) ((atExpr p (.atom z)).eval u) η)
    (b : RatPresentation) (hb : r^2 ≤ b.value)
    (hDen : m ≤ ((atExpr (vanishing (old.map Expr.atom)) (.atom z)).eval u).normSq b) :
    m ≤ distanceLe
      (mixedPolynomialEval ((displacement p (old.map Expr.atom) (.atom z) (.atom y)).map
        (Expr.eval u)) (u w))
      (mixedPolynomialEval (p.map (Expr.eval u)) (u w)) e := by
  let c := atExpr p (.atom z)
  let d := atExpr (vanishing (old.map Expr.atom)) (.atom z)
  let q := displacement p (old.map Expr.atom) (.atom z) (.atom y)
  have hAt (i : V) : (Expr.atom i).Safe u m := by
    intro a ha
    exact (List.not_mem_nil ha).elim
  have hOldSafe : CoeffSafe u m (old.map Expr.atom) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact hAt i
  have hC : c.Safe u m := atExpr_safe hp (hAt z)
  have hD : d.Safe u m := atExpr_safe (coeffSafe_vanishing hOldSafe) (hAt z)
  have hb₀ : 0 < b.value := (pow_pos hr 2).trans_le hb
  have hPos : m ≤ positiveCutValue (d.eval u).normSq := hDen.trans (le_iSup (fun r : {r : RatPresentation // 0 < r.value} => (d.eval u).normSq r.val) ⟨b,hb₀⟩)
  have hQ : CoeffSafe u m q := coeffSafe_displacement hp hOldSafe (hAt z) (hAt y) hPos
  have hAux : ∀ a ∈ [c,d], a.Safe u m := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    · exact hC
    · exact hD
  have hLw := expr_distance_forced_with_aux u m (atExpr q (.atom w))
    (atExpr p (.atom w)) [c,d] e hu (atExpr_safe hQ (hAt w)) (atExpr_safe hp (hAt w)) hAux (by
      intro k x hk hNZ hkm hx hTrace
      have hTc := hTrace c List.mem_cons_self
      have hTd := hTrace d (List.mem_cons_of_mem _ List.mem_cons_self)
      have hCValid := c.eval_cutOn u m hu hC
      have hDValid := d.eval_cutOn u m hu hD
      have hZero := checked_complex_traces k 0
      have hZValid := ComplexBits.checked_cutOn 0 m
      have hNN : ∀ i ∈ old, ‖x i‖ ≤ (L : ℝ) := by
        intro i hi
        have h' := trace_distanceLe hk hNZ hkm (hu i) hZValid (hx i) hZero hL (hOld i hi)
        simpa only [dist_zero_right] using h'
      have hWW : ‖x w‖ ≤ (R : ℝ) := by
        simpa only [dist_zero_right] using
          trace_distanceLe hk hNZ hkm (hu w) hZValid (hx w) hZero hR hW
      have hShift := trace_distanceLe hk hNZ hkm (hu y) hCValid
        (hx y) hTc hη hNear
      have hDenSq := trace_forcedMember_le hk hNZ (hTd.normSq hk hkm hDValid)
        b ⟨0,(hkm 0).trans hDen⟩
      have hR' : 0 ≤ (R : ℝ) := by exact_mod_cast hR
      have hL' : 0 ≤ (L : ℝ) := by exact_mod_cast hL
      have hη' : 0 ≤ (η : ℝ) := by exact_mod_cast hη
      have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
      have hb' : (r : ℝ)^2 ≤ (b.value : ℝ) := by exact_mod_cast hb
      have hNorm : (r : ℝ) ≤ ‖d.evalGround x‖ := by
        have hSq : (r : ℝ)^2 ≤ ‖d.evalGround x‖^2 :=
          hb'.trans (by simpa only [Complex.normSq_eq_norm_sq] using hDenSq)
        by_contra hlt
        have hG := lt_of_not_ge hlt
        nlinarith [mul_pos (sub_pos.mpr hG)
          (add_pos_of_pos_of_nonneg hr' (norm_nonneg (d.evalGround x)))]
      have hDP : 0 < ‖d.evalGround x‖ := hr'.trans_le hNorm
      have hNum : ‖x y - c.evalGround x‖ ≤ (η : ℝ) := by
        simpa only [dist_eq_norm] using hShift
      have hDiv : ‖x y - c.evalGround x‖ / ‖d.evalGround x‖ ≤ (η : ℝ) / (r : ℝ) := by
        apply (div_le_div_iff₀ hDP hr').mpr
        exact (mul_le_mul_of_nonneg_right hNum hr'.le).trans
          (mul_le_mul_of_nonneg_left hNorm hη')
      have hProd := scalar_anchor_bound x old w hR' hL' hWW hNN
      have hQuant' : (η : ℝ) * ((R : ℝ) + (L : ℝ))^old.length ≤ (e : ℝ) * (r : ℝ) := by
        exact_mod_cast hQuant
      have hErr : (η : ℝ) / (r : ℝ) * ((R : ℝ) + (L : ℝ))^old.length ≤ (e : ℝ) := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hr').mpr hQuant'
      let A := (old.map (fun i => x w - x i)).prod
      let G := (x y - c.evalGround x) / d.evalGround x * A
      have hDG : d.evalGround x = (old.map (fun i => x z - x i)).prod := by
        unfold d
        rw [atExpr_vanishing,List.map_map]
        rfl
      have hV : (atExpr q (.atom w)).evalGround x = (atExpr p (.atom w)).evalGround x + G := by
        unfold q
        rw [atExpr_displacement]
        simp only [G,A,c,hDG,List.map_map,Function.comp_apply,Expr.evalGround]
        rfl
      calc
        dist ((atExpr q (.atom w)).evalGround x) ((atExpr p (.atom w)).evalGround x) = ‖G‖ := by
          rw [hV, dist_eq_norm]
          congr 1
          abel
        _ = (‖x y - c.evalGround x‖ / ‖d.evalGround x‖) * ‖A‖ := by
          simp only [G,Complex.norm_mul,Complex.norm_div]
        _ ≤ (η : ℝ) / (r : ℝ) * ((R : ℝ) + (L : ℝ))^old.length :=
          mul_le_mul hDiv hProd (norm_nonneg _) (div_nonneg hη' hr'.le)
        _ ≤ (e : ℝ) := hErr)
  simpa only [q,atExpr_eval,Expr.eval] using hLw

end ExprPoly

end JSP000930.Negative
