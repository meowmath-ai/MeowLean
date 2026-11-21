import JSP000930NegativeSpliceExpressionRing

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private abbrev PatchIndex (a h g : List (ComplexBits B)) :=
  Fin a.length ⊕ (Fin h.length ⊕ Fin g.length)

private def patchCoeffEnv (a h g : List (ComplexBits B)) : PatchIndex a h g → ComplexBits B
  | .inl i => a[i.val]
  | .inr (.inl i) => h[i.val]
  | .inr (.inr i) => g[i.val]

private def patchLeft (a h g : List (ComplexBits B)) : ExprPoly.Poly (PatchIndex a h g) :=
  List.ofFn (fun i : Fin a.length => Expr.atom (.inl i))

private def patchMid (a h g : List (ComplexBits B)) : ExprPoly.Poly (PatchIndex a h g) :=
  List.ofFn (fun i : Fin h.length => Expr.atom (.inr (.inl i)))

private def patchGuard (a h g : List (ComplexBits B)) : ExprPoly.Poly (PatchIndex a h g) :=
  List.ofFn (fun i : Fin g.length => Expr.atom (.inr (.inr i)))

noncomputable def namedSpliceCoefficients (a h g : List (ComplexBits B)) : List (ComplexBits B) :=
  (patchPoly (patchLeft a h g) (patchMid a h g) (patchGuard a h g)).map (Expr.eval (patchCoeffEnv a h g))

noncomputable def spliceValue (a h g : ComplexBits B) : ComplexBits B :=
  a.add (g.mul (h.add a.neg))

theorem namedSpliceCoefficients_eval
    (a h g : List (ComplexBits B)) (z : ComplexBits B) (m : B)
    (ha : ∀ c ∈ a,c.CutOn m) (hh : ∀ c ∈ h,c.CutOn m)
    (hg : ∀ c ∈ g,c.CutOn m) (hz : z.CutOn m) :
    (∀ c ∈ namedSpliceCoefficients a h g,c.CutOn m) ∧
    m ≤ (mixedPolynomialEval (namedSpliceCoefficients a h g) z).name =ᴮ
      (spliceValue (mixedPolynomialEval a z) (mixedPolynomialEval h z) (mixedPolynomialEval g z)).name := by
  let V := PatchIndex a h g
  let u := patchCoeffEnv a h g
  let v : Option V → ComplexBits B
    | none => z
    | some i => u i
  let A := patchLeft a h g
  let H := patchMid a h g
  let G := patchGuard a h g
  let A' := A.map (Expr.rename some)
  let H' := H.map (Expr.rename some)
  let G' := G.map (Expr.rename some)
  let Z : Expr (Option V) := .atom none
  have hU : ∀ i,(u i).CutOn m := by
    intro i
    rcases i with i | (i | i)
    · exact ha _ (List.getElem_mem i.isLt)
    · exact hh _ (List.getElem_mem i.isLt)
    · exact hg _ (List.getElem_mem i.isLt)
  have hV : ∀ i,(v i).CutOn m := by
    intro i
    cases i with
    | none => exact hz
    | some i => exact hU i
  have hAtom (i : Option V) : (Expr.atom i).Safe v m := by
    intro d hd
    exact (List.not_mem_nil hd).elim
  have hA : CoeffSafe v m A' := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hAtom _
  have hH : CoeffSafe v m H' := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hAtom _
  have hG : CoeffSafe v m G' := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hAtom _
  let L := patchPoly A' H' G'
  have hL : CoeffSafe v m L := patchPoly_safe hA hH hG
  have hCompiled : L.map (Expr.eval v) = namedSpliceCoefficients a h g := by
    change (patchPoly A' H' G').map (Expr.eval v) = (patchPoly A H G).map (Expr.eval u)
    rw [← patchPoly_rename,List.map_map]
    apply List.map_congr_left
    intro c _
    exact Expr.eval_rename some v c
  have hAc : A'.map (Expr.eval v) = a := by
    simp only [A',A,patchLeft,List.map_ofFn,Function.comp_apply,Expr.rename,Expr.eval,v,u,patchCoeffEnv,
      List.ofFn_getElem]
    exact List.ofFn_getElem
  have hHc : H'.map (Expr.eval v) = h := by
    simp only [H',H,patchMid,List.map_ofFn,Function.comp_apply,Expr.rename,Expr.eval,v,u,patchCoeffEnv,
      List.ofFn_getElem]
    exact List.ofFn_getElem
  have hGc : G'.map (Expr.eval v) = g := by
    simp only [G',G,patchGuard,List.map_ofFn,Function.comp_apply,Expr.rename,Expr.eval,v,u,patchCoeffEnv,
      List.ofFn_getElem]
    exact List.ofFn_getElem
  refine ⟨?_,?_⟩
  · intro c hc
    rw [← hCompiled] at hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
    exact e.eval_cutOn v m hV (hL e he)
  · let E := atExpr A' Z
    let F := atExpr H' Z
    let M := atExpr G' Z
    let D := Expr.add E (Expr.mul M (Expr.add F (Expr.neg E)))
    have eSafe := atExpr_safe hA (hAtom none)
    have fSafe := atExpr_safe hH (hAtom none)
    have mSafe := atExpr_safe hG (hAtom none)
    have dSafe : D.Safe v m := safe_add eSafe (safe_mul mSafe (safe_add fSafe (safe_neg eSafe)))
    have ht := expr_eq_forced v m (atExpr L Z) D hV (atExpr_safe hL (hAtom none)) dSafe (by
      intro p w _ _ _ _
      unfold L D
      rw [atExpr_patchPoly]
      change _ = (atExpr A' Z).evalGround w + (atExpr G' Z).evalGround w *
        ((atExpr H' Z).evalGround w + -(atExpr A' Z).evalGround w)
      rw [sub_eq_add_neg])
    simpa only [D,E,F,M,atExpr_eval,Expr.eval,Z,v,hCompiled,hAc,hHc,hGc,spliceValue] using ht

end JSP000930.Negative
