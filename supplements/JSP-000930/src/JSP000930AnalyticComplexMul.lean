import JSP000930AnalyticRealSelectors
import Mathlib.Tactic.IrreducibleDef

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private noncomputable irreducible_def markedTruth {n : ℕ}
    (p : B) (v : DVec (V B) n) (f : SForm n) : B := p ⊓ bTruth v f

private theorem markedSelectMul {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i j : Fin k) (u w : RatPresentation → B) (p : B)
    (hi : bTerm v (ps i) = weightedRationalSet u)
    (hj : bTerm v (ps j) = weightedRationalSet w)
    (hu : ProperCutOn p u) (hw : ProperCutOn p w) :
    markedTruth p v (selectReal_f ps (fun a r => realMul_f (a i) (a j) r) D) =
      markedTruth p (DVec.cons (mulCutName u w) v)
        (D (fun a => up (ps a)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  simp only [markedTruth_def]
  exact bTruth_selectMul_weighted v ps D i j u w p hi hj hu hw

private theorem markedSelectNeg {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i : Fin k) (u : RatPresentation → B) (p : B)
    (hi : bTerm v (ps i) = weightedRationalSet u) (hu : ProperCutOn p u) :
    markedTruth p v (selectReal_f ps (fun a r => realNeg_f (a i) r) D) =
      markedTruth p (DVec.cons (negCutName u) v)
        (D (fun a => up (ps a)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  simp only [markedTruth_def]
  exact bTruth_selectNeg_weighted v ps D i u p hi hu

private theorem bTerm_pushCutMatrix {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n) (cuts : Fin k → RatPresentation → B)
    (w : RatPresentation → B)
    (h : ∀ i, bTerm v (ps i) = weightedRationalSet (cuts i))
    (i : Fin (k+1)) :
    bTerm (DVec.cons (weightedRationalSet w) v)
      (Fin.snoc (α := fun _ => STerm (n+1)) (fun j => up (ps j)) (bd_var ⟨0,Nat.succ_pos n⟩) i) =
      weightedRationalSet (Fin.snoc (α := fun _ => RatPresentation → B) cuts w i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have ht : Fin.snoc (α := fun _ => STerm (n+1)) (fun j => up (ps j))
        (bd_var ⟨0,Nat.succ_pos n⟩) (Fin.last k) = bd_var ⟨0,Nat.succ_pos n⟩ :=
      Fin.snoc_last _ _
    have hc : Fin.snoc (α := fun _ => RatPresentation → B) cuts w (Fin.last k) = w :=
      Fin.snoc_last _ _
    exact (congrArg (bTerm (DVec.cons (weightedRationalSet w) v)) ht).trans
      ((bTerm_current_r181 v (weightedRationalSet w)).trans (congrArg weightedRationalSet hc).symm)
  · have ht : Fin.snoc (α := fun _ => STerm (n+1)) (fun j => up (ps j))
        (bd_var ⟨0,Nat.succ_pos n⟩) j.castSucc = up (ps j) :=
      Fin.snoc_castSucc _ _ _
    have hc : Fin.snoc (α := fun _ => RatPresentation → B) cuts w j.castSucc = cuts j :=
      Fin.snoc_castSucc _ _ _
    exact (congrArg (bTerm (DVec.cons (weightedRationalSet w) v)) ht).trans
      ((bTerm_up_r181 v (weightedRationalSet w) (ps j)).trans
        ((h j).trans (congrArg weightedRationalSet hc).symm))

set_option maxHeartbeats 1000000 in
theorem bTruth_complexMulCore_weighted {n : ℕ} (v : DVec (V B) n)
    (P : Fin 6 → STerm n) (a b c : ComplexBits B) (p : B)
    (h : ∀ i, bTerm v (P i) = weightedRationalSet (cutTripleMatrix a b c i))
    (ha : a.CutOn p) (hb : b.CutOn p) :
    p ⊓ bTruth v (complexMulCore_f P) = p ⊓ (c.name =ᴮ (a.mul b).name) := by
  let F := cutTripleMatrix a b c
  let u1 : RatPresentation → B := mulCutBits a.re b.re
  let u2 : RatPresentation → B := mulCutBits a.im b.im
  let u3 : RatPresentation → B := negCutBits u2
  let u4 : RatPresentation → B := mulCutBits a.re b.im
  let u5 : RatPresentation → B := mulCutBits a.im b.re
  have hu1 : ProperCutOn p u1 := mulCutBits_properCut _ _ p ha.1 hb.1
  have hu2 : ProperCutOn p u2 := mulCutBits_properCut _ _ p ha.2 hb.2
  have hu3 : ProperCutOn p u3 := negCutBits_properCut _ p hu2
  have hu4 : ProperCutOn p u4 := mulCutBits_properCut _ _ p ha.1 hb.2
  have hu5 : ProperCutOn p u5 := mulCutBits_properCut _ _ p ha.2 hb.1
  let v1 : DVec (V B) (n+1) := DVec.cons (mulCutName a.re b.re) v
  let T1 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let P1 : Fin 7 → STerm (n+1) :=
    ![up (P 0),up (P 1),up (P 2),up (P 3),up (P 4),up (P 5),T1]
  let F1 : Fin 7 → RatPresentation → B :=
    ![F 0,F 1,F 2,F 3,F 4,F 5,u1]
  have hP1 : Fin.snoc (fun j => up (P j)) T1 = P1 := by
    funext j
    fin_cases j <;> rfl
  have hF1 : Fin.snoc F u1 = F1 := by
    funext j
    fin_cases j <;> rfl
  have h1 (j : Fin 7) : bTerm v1 (P1 j) = weightedRationalSet (F1 j) := by
    rw [← hP1, ← hF1]
    exact bTerm_pushCutMatrix v P F u1 h j
  let v2 : DVec (V B) (n+2) := DVec.cons (mulCutName a.im b.im) v1
  let T2 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let P2 : Fin 8 → STerm (n+2) :=
    ![up (P1 0),up (P1 1),up (P1 2),up (P1 3),up (P1 4),up (P1 5),up (P1 6),T2]
  let F2 : Fin 8 → RatPresentation → B :=
    ![F1 0,F1 1,F1 2,F1 3,F1 4,F1 5,F1 6,u2]
  have hP2 : Fin.snoc (fun j => up (P1 j)) T2 = P2 := by
    funext j
    fin_cases j <;> rfl
  have hF2 : Fin.snoc F1 u2 = F2 := by
    funext j
    fin_cases j <;> rfl
  have h2 (j : Fin 8) : bTerm v2 (P2 j) = weightedRationalSet (F2 j) := by
    rw [← hP2, ← hF2]
    exact bTerm_pushCutMatrix v1 P1 F1 u2 h1 j
  let v3 : DVec (V B) (n+3) := DVec.cons (negCutName u2) v2
  let T3 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let P3 : Fin 8 → STerm (n+3) :=
    ![up (P2 0),up (P2 1),up (P2 2),up (P2 3),up (P2 4),up (P2 5),up (P2 6),T3]
  let F3 : Fin 8 → RatPresentation → B :=
    ![F2 0,F2 1,F2 2,F2 3,F2 4,F2 5,F2 6,u3]
  have hP3 : Fin.snoc (fun j => up ((fun j : Fin 7 => P2 j.castSucc) j)) T3 = P3 := by
    funext j
    fin_cases j <;> rfl
  have hF3 : Fin.snoc (fun j : Fin 7 => F2 j.castSucc) u3 = F3 := by
    funext j
    fin_cases j <;> rfl
  have h3 (j : Fin 8) : bTerm v3 (P3 j) = weightedRationalSet (F3 j) := by
    rw [← hP3, ← hF3]
    exact bTerm_pushCutMatrix v2 (fun j : Fin 7 => P2 j.castSucc) (fun j : Fin 7 => F2 j.castSucc) u3 (fun j : Fin 7 => h2 j.castSucc) j
  let v4 : DVec (V B) (n+4) := DVec.cons (mulCutName a.re b.im) v3
  let T4 : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let P4 : Fin 9 → STerm (n+4) :=
    ![up (P3 0),up (P3 1),up (P3 2),up (P3 3),up (P3 4),up (P3 5),up (P3 6),up (P3 7),T4]
  let F4 : Fin 9 → RatPresentation → B :=
    ![F3 0,F3 1,F3 2,F3 3,F3 4,F3 5,F3 6,F3 7,u4]
  have hP4 : Fin.snoc (fun j => up (P3 j)) T4 = P4 := by
    funext j
    fin_cases j <;> rfl
  have hF4 : Fin.snoc F3 u4 = F4 := by
    funext j
    fin_cases j <;> rfl
  have h4 (j : Fin 9) : bTerm v4 (P4 j) = weightedRationalSet (F4 j) := by
    rw [← hP4, ← hF4]
    exact bTerm_pushCutMatrix v3 P3 F3 u4 h3 j
  let v5 : DVec (V B) (n+5) := DVec.cons (mulCutName a.im b.re) v4
  let T5 : STerm (n+5) := bd_var ⟨0,Nat.succ_pos (n+4)⟩
  let addParts {d : ℕ} (s : Fin 9 → STerm d) (bc : STerm d) : SForm d :=
    bd_and (realAdd_f (s 6) (s 7) (s 4)) (realAdd_f (s 8) bc (s 5))
  let afterAD {d : ℕ} (s : Fin 8 → STerm d) (ad : STerm d) : SForm d :=
    selectReal_f (fun i => ![s 0,s 1,s 2,s 3,s 4,s 5,s 6,s 7,ad] i)
      (fun t bc => realMul_f (t 1) (t 2) bc) @addParts
  let afterNeg {d : ℕ} (s : Fin 8 → STerm d) (nbd : STerm d) : SForm d :=
    selectReal_f (fun i => ![s 0,s 1,s 2,s 3,s 4,s 5,s 6,nbd] i)
      (fun t ad => realMul_f (t 0) (t 3) ad) @afterAD
  let afterBD {d : ℕ} (s : Fin 7 → STerm d) (bd : STerm d) : SForm d :=
    selectReal_f (fun i => ![s 0,s 1,s 2,s 3,s 4,s 5,s 6,bd] i)
      (fun t nbd => realNeg_f (t 7) nbd) @afterNeg
  let afterAC {d : ℕ} (s : Fin 6 → STerm d) (ac : STerm d) : SForm d :=
    selectReal_f (fun i => ![s 0,s 1,s 2,s 3,s 4,s 5,ac] i)
      (fun t bd => realMul_f (t 1) (t 3) bd) @afterBD
  have hCore : complexMulCore_f P =
      selectReal_f P (fun s ac => realMul_f (s 0) (s 2) ac) @afterAC := rfl
  rw [hCore, ← markedTruth_def]
  refine Eq.trans (markedSelectMul v P @afterAC 0 2 a.re b.re p
    (h 0) (h 2) ha.1 hb.1) ?_
  have align1 : afterAC (fun j => up (P j)) T1 =
      selectReal_f P1 (fun s bd => realMul_f (s 1) (s 3) bd) @afterBD := rfl
  change markedTruth p v1 (afterAC (fun j => up (P j)) T1) = _
  rw [align1]
  refine Eq.trans (markedSelectMul v1 P1 @afterBD 1 3 a.im b.im p
    (h1 1) (h1 3) ha.2 hb.2) ?_
  have align2 : afterBD (fun j => up (P1 j)) T2 =
      selectReal_f P2 (fun s nbd => realNeg_f (s 7) nbd) @afterNeg := rfl
  change markedTruth p v2 (afterBD (fun j => up (P1 j)) T2) = _
  rw [align2]
  refine Eq.trans (markedSelectNeg v2 P2 @afterNeg 7 u2 p (h2 7) hu2) ?_
  have align3 : afterNeg (fun j => up (P2 j)) T3 =
      selectReal_f P3 (fun s ad => realMul_f (s 0) (s 3) ad) @afterAD := rfl
  change markedTruth p v3 (afterNeg (fun j => up (P2 j)) T3) = _
  rw [align3]
  refine Eq.trans (markedSelectMul v3 P3 @afterAD 0 3 a.re b.im p
    (h3 0) (h3 3) ha.1 hb.2) ?_
  have align4 : afterAD (fun j => up (P3 j)) T4 =
      selectReal_f P4 (fun s bc => realMul_f (s 1) (s 2) bc) @addParts := rfl
  change markedTruth p v4 (afterAD (fun j => up (P3 j)) T4) = _
  rw [align4]
  refine Eq.trans (markedSelectMul v4 P4 @addParts 1 2 a.im b.re p
    (h4 1) (h4 2) ha.2 hb.1) ?_
  rw [markedTruth_def]
  let t(i : Fin 9) : STerm (n+5) := up (P4 i)
  have ht (i : Fin 9) : bTerm v5 (t i) = weightedRationalSet (F4 i) :=
    (bTerm_up_r181 v4 (mulCutName a.im b.re) (P4 i)).trans (h4 i)
  change p ⊓ bTruth v5 (bd_and (realAdd_f (t 6) (t 7) (t 4))
    (realAdd_f (t 8) T5 (t 5))) = _
  have hAnd : bTruth v5 (bd_and (realAdd_f (t 6) (t 7) (t 4))
      (realAdd_f (t 8) T5 (t 5))) =
      bTruth v5 (realAdd_f (t 6) (t 7) (t 4)) ⊓ bTruth v5 (realAdd_f (t 8) T5 (t 5)) :=
    boolean_realize_bounded_formula_and
  rw [hAnd,bTruth_realAdd_weighted v5 (t 6) (t 7) (t 4) u1 u3 c.re (ht 6) (ht 7) (ht 4),
    bTruth_realAdd_weighted v5 (t 8) T5 (t 5) u4 u5 c.im (ht 8)
      (bTerm_current_r181 v4 (mulCutName a.im b.re)) (ht 5),ComplexBits.name_eq] <;> rfl

theorem bTruth_complexMul_weighted {n : ℕ} (v : DVec (V B) n)
    (A C D : STerm n) (a c d : ComplexBits B) (p : B)
    (hA : bTerm v A = a.name) (hC : bTerm v C = c.name) (hD : bTerm v D = d.name)
    (ha : a.CutOn p) (hc : c.CutOn p) (hd : d.CutOn p) :
    p ⊓ bTruth v (complexMul_f A C D) = p ⊓ (d.name =ᴮ (a.mul c).name) := by
  unfold complexMul_f
  rw [bTruth_complexTriple_weighted v A C D _ a c d p hA hC hD ha hc hd]
  exact bTruth_complexMulCore_weighted (complexTripleEnv v a c d) complexTripleMatrix
    a c d p (bTerm_complexTripleMatrix v a c d) ha hc

end JSP000930.AnalyticSyntax
