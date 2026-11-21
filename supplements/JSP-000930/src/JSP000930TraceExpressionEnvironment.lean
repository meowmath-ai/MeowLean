import JSP000930FiniteExpressionSupport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev TraceAtoms (p : PolyTrace B J) :=
  Fin p.coeff.length ⊕ ({i : J // i ∈ p.pins} ⊕ (Bool ⊕ RatGrid p.radius))

def siteAtom (p : PolyTrace B J) (i : {i : J // i ∈ p.pins}) : TraceAtoms p :=
  Sum.inr (Sum.inl i)

def newSiteAtom (p : PolyTrace B J) : TraceAtoms p := Sum.inr (Sum.inr (Sum.inl false))

def newValueAtom (p : PolyTrace B J) : TraceAtoms p := Sum.inr (Sum.inr (Sum.inl true))

def gridAtom (p : PolyTrace B J) (g : RatGrid p.radius) : TraceAtoms p :=
  Sum.inr (Sum.inr (Sum.inr g))

noncomputable def oldSiteAtoms (p : PolyTrace B J) : List (TraceAtoms p) :=
  p.pins.attach.toList.map (siteAtom p)

def coefficientAtoms (p : PolyTrace B J) : ExprPoly.Poly (TraceAtoms p) :=
  List.ofFn (fun i : Fin p.coeff.length => Expr.atom (Sum.inl i))

noncomputable def traceEnv (p : PolyTrace B J) (site : J → ComplexBits B) (z : J)
    (target : ComplexBits B) : TraceAtoms p → ComplexBits B
  | .inl i => p.coeff[i.val]'i.2
  | .inr (.inl i) => site i.1
  | .inr (.inr (.inl false)) => site z
  | .inr (.inr (.inl true)) => target
  | .inr (.inr (.inr g)) => ComplexBits.checked (gridPoint g)

theorem coefficientAtoms_eval (p : PolyTrace B J) (site : J → ComplexBits B) (z : J)
    (target : ComplexBits B) :
    (coefficientAtoms p).map (Expr.eval (traceEnv p site z target)) = p.coeff := by
  rw [coefficientAtoms,List.map_ofFn]
  exact List.ofFn_getElem

theorem mem_oldSiteAtoms (p : PolyTrace B J) (i : {i : J // i ∈ p.pins}) :
    siteAtom p i ∈ oldSiteAtoms p := by
  apply List.mem_map.mpr
  exact ⟨i,Finset.mem_toList.mpr (Finset.mem_attach _ _),rfl⟩

theorem oldSiteAtoms_mem (p : PolyTrace B J) {a : TraceAtoms p} (h : a ∈ oldSiteAtoms p) :
    ∃ i : {i : J // i ∈ p.pins}, siteAtom p i = a := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp h
  exact ⟨i,he⟩

noncomputable def traceDenominator (p : PolyTrace B J) : Expr (TraceAtoms p) :=
  ExprPoly.atExpr (ExprPoly.vanishing ((oldSiteAtoms p).map Expr.atom)) (.atom (newSiteAtom p))

theorem traceEnv_denominator_target_irrelevant (p : PolyTrace B J)
    (site : J → ComplexBits B) (z : J) (x y : ComplexBits B) :
    (traceDenominator p).eval (traceEnv p site z x) =
      (traceDenominator p).eval (traceEnv p site z y) := by
  let P : TraceAtoms p → Prop := fun a => a ≠ newValueAtom p
  apply (traceDenominator p).eval_eq_of_only (P := P)
  · refine ExprPoly.atExpr_only (ExprPoly.coeffOnly_vanishing ?_) ?_
    · intro a ha
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      obtain ⟨j,rfl⟩ := oldSiteAtoms_mem p hi
      change siteAtom p j ≠ newValueAtom p
      simp [siteAtom,newValueAtom]
    · change newSiteAtom p ≠ newValueAtom p
      simp [newSiteAtom,newValueAtom]
  · intro a ha
    rcases a with i | a
    · rfl
    rcases a with i | a
    · rfl
    rcases a with b | g
    · cases b
      · rfl
      · exact (ha rfl).elim
    · rfl

end JSP000930.Negative
