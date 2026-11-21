import JSP000930SymbolicPrecision
import JSP000930ExpressionContextRename

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly JSP000933.CantorCodes

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

structure NamedSpliceGuard (site : J → ComplexBits B)
    (z : J) (old : List J) (R : ℕ) (m : B) where
  coeff : List (ComplexBits B)
  bound : ℚ
  bound_one : 1 ≤ bound
  coeff_cut : ∀ c ∈ coeff,c.CutOn m
  at_new : m ≤ (mixedPolynomialEval coeff (site z)).name =ᴮ (ComplexBits.checked (0 : ℂ)).name
  at_old : ∀ i ∈ old,m ≤ (mixedPolynomialEval coeff (site i)).name =ᴮ
    (ComplexBits.checked (1 : ℂ)).name
  grid_bound : ∀ g : RatGrid R,m ≤ distanceLe
    (mixedPolynomialEval coeff (ComplexBits.checked (gridPoint g))) (ComplexBits.checked (0 : ℂ)) bound

private abbrev GuardAtom (old : List J) := Fin old.length ⊕ Bool

private def guardAtoms (old : List J) : List (GuardAtom old) :=
  List.ofFn Sum.inl

private noncomputable def guardEnv (site : J → ComplexBits B) (z : J) (old : List J) :
    GuardAtom old → ComplexBits B
  | .inl i => site old[i.val]
  | .inr false => site z
  | .inr true => ComplexBits.checked 0

private theorem guardAtom_mem (old : List J) (i : Fin old.length) :
    Sum.inl i ∈ guardAtoms old :=
  List.mem_ofFn.mpr ⟨i,rfl⟩

private theorem guard_atom_safe {V : Type} (u : V → ComplexBits B) (m : B) (a : V) :
    (Expr.atom a).Safe u m := by
  intro d hd
  exact (List.not_mem_nil hd).elim

private theorem guard_one_coeff_safe {V : Type} (u : V → ComplexBits B) (m : B) :
    CoeffSafe u m ([ExprPoly.one] : ExprPoly.Poly V) := by
  intro a ha
  obtain rfl := List.mem_singleton.mp ha
  intro d hd
  exact (List.not_mem_nil hd).elim

private theorem guard_one_eval {V : Type} [Countable V] [Nonempty V]
    (u : V → ComplexBits B) (m : B) (hu : ∀ i,(u i).CutOn m) (i : V) :
    m ≤ (mixedPolynomialEval (([ExprPoly.one] : ExprPoly.Poly V).map (Expr.eval u)) (u i)).name =ᴮ
      (ComplexBits.checked (1 : ℂ)).name := by
  let a := atExpr ([ExprPoly.one] : ExprPoly.Poly V) (.atom i)
  let b : Expr V := .num 1 0
  have ha := atExpr_safe (guard_one_coeff_safe u m) (guard_atom_safe u m i)
  have hb : b.Safe u m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have h := expr_eq_forced u m a b hu ha hb (by
    intro q x _ _ _ _
    change ExprPoly.one.evalGround x + x i * ExprPoly.zero.evalGround x = ExprPoly.one.evalGround x
    simp only [ground_zero,mul_zero,add_zero])
  simpa only [a,b,atExpr_eval,Expr.eval,ExprPoly.one,ComplexBits.checked,Complex.one_re,Complex.one_im,
    Rat.cast_one,Rat.cast_zero] using h

private theorem guard_plus_rename {V W : Type} (f : V → W) (p q : ExprPoly.Poly V) :
    (plus p q).map (Expr.rename f) = plus (p.map (Expr.rename f)) (q.map (Expr.rename f)) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      change Expr.add (a.rename f) (b.rename f) :: (plus p q).map (Expr.rename f) =
        Expr.add (a.rename f) (b.rename f) :: plus (p.map (Expr.rename f)) (q.map (Expr.rename f))
      rw [ih]

private theorem guard_scale_rename {V W : Type} (f : V → W) (a : Expr V) (p : ExprPoly.Poly V) :
    (scale a p).map (Expr.rename f) = scale (a.rename f) (p.map (Expr.rename f)) := by
  simp only [scale,List.map_map]
  rfl

private theorem guard_vanishing_rename {V W : Type} (f : V → W) (l : List V) :
    (vanishing (l.map Expr.atom)).map (Expr.rename f) = vanishing ((l.map f).map Expr.atom) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,vanishing,linearMul,guard_plus_rename,guard_scale_rename,Expr.rename,ih] <;> rfl

private theorem guard_displacement_rename {V W : Type} (f : V → W) (p : ExprPoly.Poly V) (l : List V) (z y : V) :
    (displacement p (l.map Expr.atom) (.atom z) (.atom y)).map (Expr.rename f) =
      displacement (p.map (Expr.rename f)) ((l.map f).map Expr.atom) (.atom (f z)) (.atom (f y)) := by
  unfold displacement
  simp only [guard_plus_rename,guard_scale_rename,Expr.rename, ← atExpr_rename,guard_vanishing_rename]

theorem exists_named_splice_guard
    (site : J → ComplexBits B) (z : J) (old : List J) (R : ℕ) (m : B) (hm : m ≠ ⊥)
    (hSite : ∀ i,(site i).CutOn m)
    (hApart : ∀ i ∈ old,m ≤ ((site z).name =ᴮ (site i).name)ᶜ) :
    ∃ s : B,s ≠ ⊥ ∧ s ≤ m ∧ Nonempty (NamedSpliceGuard site z old R s) := by
  classical
  let V := GuardAtom old
  let u : V → ComplexBits B := guardEnv site z old
  let l : List V := guardAtoms old
  let Z : V := .inr false
  let Y : V := .inr true
  let p : ExprPoly.Poly V := [ExprPoly.one]
  haveI : Nonempty V := ⟨Z⟩
  have hU : ∀ i,(u i).CutOn m := by
    intro i
    rcases i with i|i
    · exact hSite _
    · cases i
      · exact hSite z
      · exact ComplexBits.checked_cutOn 0 m
  have hSep : ∀ i ∈ l,m ≤ ((u Z).name =ᴮ (u i).name)ᶜ := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact hApart _ (List.getElem_mem j.isLt)
  obtain ⟨k,L,hk,hkm,hL,hNorm⟩ := exists_finite_normBound u l m hm hU
  have hPos := named_vanishing_positive u Z l m hU hSep
  obtain ⟨d,s,hs,hsk,hsD⟩ := exists_nonzero_below_choice_r135 k hk
    (fun d : {d : RatPresentation // 0 < d.value} =>
      ((atExpr (vanishing (l.map Expr.atom)) (.atom Z)).eval u).normSq d.1) (hkm.trans hPos)
  have hsm := hsk.trans hkm
  let r := min (1 : ℚ) d.1.value / 2
  have hr : 0 < r := div_pos (lt_min zero_lt_one d.2) (by norm_num)
  have hr' : r ≤ min 1 d.1.value := by
    dsimp [r]
    linarith [lt_min (show (0 : ℚ) < 1 by norm_num) d.2]
  have hrSq : r^2 ≤ d.1.value :=
    (show r^2 ≤ r by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_left (hr'.trans (min_le_left _ _)) hr.le).trans_eq (mul_one r)
      ).trans (hr'.trans (min_le_right _ _))
  let E := ((R : ℚ) + L)^l.length / r
  have hE : (0 : ℚ) ≤ E := div_nonneg (pow_nonneg (add_nonneg (by positivity) hL) _) hr.le
  have hQuant : 1 * ((R : ℚ) + L)^l.length ≤ E*r := by
    dsimp [E]
    rw [one_mul,div_mul_cancel₀ _ hr.ne']
  have hUs : ∀ i,(u i).CutOn s := fun i => cutOn_mono930 (hU i) hsm
  obtain ⟨g,hg,hGC,hGZ,hGL⟩ := named_one_pin_exact u s p l Z Y hUs
    (guard_one_coeff_safe u s) (fun i hi => hsm.trans (hSep i hi))
  refine ⟨s,hs,hsm,⟨⟨g,E+1,by linarith,hGC,hGZ,?_,?_⟩⟩⟩
  · intro j hj
    obtain ⟨i,hi,hij⟩ := List.getElem_of_mem hj
    let a : Fin old.length := ⟨i,hi⟩
    have he : u (.inl a) = site j := congrArg site hij
    have h := bSet.bv_trans (hGL (.inl a) (guardAtom_mem old a))
      (guard_one_eval u s hUs (.inl a))
    simpa only [he] using h
  · intro x
    let v : Option V → ComplexBits B
      | none => ComplexBits.checked (gridPoint x)
      | some i => u i
    have hV : ∀ i,(v i).CutOn s := by
      intro i
      cases i with
      | none => exact ComplexBits.checked_cutOn _ s
      | some i => exact hUs i
    let p' : ExprPoly.Poly (Option V) := [ExprPoly.one]
    have hOne : s ≤ ((atExpr p' (.atom (some Z))).eval v).name =ᴮ
        (ComplexBits.checked (1 : ℂ)).name := by
      rw [atExpr_eval]
      exact guard_one_eval v s hV (some Z)
    have hN : s ≤ distanceLe (v (some Y)) ((atExpr p' (.atom (some Z))).eval v) 1 := by
      have hC : s ≤ distanceLe (v (some Y)) (ComplexBits.checked (1 : ℂ)) 1 := by
        apply checked_distanceLe
        simp
      exact distanceLe_congr_right930 (hV (some Y)) (ComplexBits.checked_cutOn 1 s)
        ((atExpr p' (.atom (some Z))).eval_cutOn v s hV
          (atExpr_safe (guard_one_coeff_safe v s) (guard_atom_safe v s (some Z))))
        (bSet.bv_symm hOne) (by norm_num) hC
    have hTest : s ≤ distanceLe (v none) (ComplexBits.checked (0 : ℂ)) (R : ℚ) := by
      apply checked_distanceLe
      rw [dist_zero_right,Rat.cast_natCast]
      exact gridPoint_norm_le x
    have hDL : s ≤ ((atExpr (vanishing ((l.map some).map Expr.atom)) (.atom (some Z))).eval v).normSq d.1 := by
      rw [← guard_vanishing_rename,show Expr.atom (some Z) = (Expr.atom Z).rename some from rfl,
        atExpr_rename,Expr.eval_rename]
      exact hsD
    have hD := named_displacement_disc_control v s p' (l.map some) (some Z) (some Y) none
      (R : ℚ) L 1 E r (by positivity) hL (by norm_num) hr
      (by simpa only [List.length_map] using hQuant) hV (guard_one_coeff_safe v s)
      (by intro i hi; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi; exact hsk.trans (hNorm a ha))
      hTest hN d.1 hrSq hDL
    have hName := guard_one_eval v s hV none
    have hMid : (mixedPolynomialEval (p'.map (Expr.eval v)) (v none)).CutOn s := by
      rw [← show (atExpr p' (.atom none)).eval v = mixedPolynomialEval (p'.map (Expr.eval v)) (v none) from atExpr_eval v p' (.atom none)]
      exact (atExpr p' (.atom none)).eval_cutOn v s hV
        (atExpr_safe (guard_one_coeff_safe v s) (guard_atom_safe v s none))
    have hTo0 : s ≤ distanceLe (mixedPolynomialEval (p'.map (Expr.eval v)) (v none))
        (ComplexBits.checked (0 : ℂ)) 1 := by
      apply extend_same_mark_seed_error (ComplexBits.checked_cutOn 1 s) hMid
        (ComplexBits.checked_cutOn 0 s) (bSet.bv_symm hName) (by norm_num)
      apply checked_distanceLe
      simp
    have hCoeff : (displacement p' ((l.map some).map Expr.atom) (.atom (some Z)) (.atom (some Y))).map
        (Expr.eval v) = g := by
      have hp' : p' = p.map (Expr.rename some) := rfl
      rw [hp',← guard_displacement_rename,List.map_map,hg]
      apply List.map_congr_left
      intro a _
      exact Expr.eval_rename some v a
    rw [hCoeff] at hD
    exact distanceLe_triangle
      (mixedPolynomialEval_cutOn g (v none) hGC (hV none))
      hMid (ComplexBits.checked_cutOn 0 s) hE (by norm_num) hD hTo0

end JSP000930.Negative
