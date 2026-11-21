import JSP000930RetargetedRefinesIncoming

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

private def SiteOnly {p : SymbolicTrace J} (a : SymbolIndex p) : Prop :=
  ∃ i : PinNumber p,Sum.inl i = a

theorem symbolicDenominator_only_sites (p : SymbolicTrace J) (i : PinNumber p) :
    (symbolicDenominator p i).Only (@SiteOnly _ p) := by
  refine atExpr_only (p := symbolicVanish p i) (z := .atom (.inl i)) ?_ ?_
  swap
  · exact ⟨i,rfl⟩
  apply coeffOnly_vanishing
  intro u hu
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
  obtain ⟨j,hj,rfl⟩ := (mem_symbolicOtherSites p i a).mp ha
  exact (show SiteOnly (Sum.inl j : SymbolIndex p) from ⟨j,rfl⟩)

theorem symbolicDenominator_eval_independent (p : SymbolicTrace J) (i : PinNumber p)
    (u v : SymbolIndex p → ComplexBits B)
    (hS : ∀ j : PinNumber p,u (.inl j) = v (.inl j)) :
    (symbolicDenominator p i).eval u = (symbolicDenominator p i).eval v :=
  (symbolicDenominator p i).eval_eq_of_only (symbolicDenominator_only_sites p i)
    (fun a ⟨j,hj⟩ => hj ▸ hS j)

structure IncomingGeometry (p : SymbolicTrace J) (site : J → ComplexBits B) (m : B) where
  L : ℚ
  r : ℚ
  one_le : 1 ≤ L
  rad_le : (p.radius : ℚ) ≤ L
  positive : 0 < r
  norms : ∀ i : PinNumber p,m ≤ distanceLe (site (pinAt p i).1)
    (ComplexBits.checked (0 : ℂ)) L
  margin : SymbolicMargin p (symbolVal p site (fun _ _ => ComplexBits.checked (0 : ℂ))) m r

theorem IncomingGeometry.margin_any (p : SymbolicTrace J) (site : J → ComplexBits B)
    (m : B) (G : IncomingGeometry p site m) (H : J → ℕ → ComplexBits B) :
    SymbolicMargin p (symbolVal p site H) m G.r := by
  intro i
  obtain ⟨b,hb,hM⟩ := G.margin i
  refine ⟨b,hb,?_⟩
  rw [symbolicDenominator_eval_independent p i
    (symbolVal p site H) (symbolVal p site (fun _ _ => ComplexBits.checked (0 : ℂ)))
    (fun j => rfl)]
  exact hM

theorem exists_incoming_geometry (p : SymbolicTrace J) (site : J → ComplexBits B)
    (m : B) (hm : m ≠ ⊥)
    (hS : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    ∃ s : B,s ≠ ⊥ ∧ s ≤ m ∧ Nonempty (IncomingGeometry p site s) := by
  let H : J → ℕ → ComplexBits B := fun _ _ => ComplexBits.checked (0 : ℂ)
  let u := symbolVal p site H
  have hu : ∀ j,(u j).CutOn m := by
    rintro (j|j)
    · exact hS _ (pinAt_mem_symbolicSite p j)
    · exact ComplexBits.checked_cutOn _ _
  have ha : ∀ j a,a ∈ symbolicOtherSites p j → m ≤ ((u (.inl j)).name =ᴮ (u a).name)ᶜ := by
    intro j a ha
    obtain ⟨k,hk,rfl⟩ := (mem_symbolicOtherSites p j a).mp ha
    exact hApart _ (pinAt_mem_symbolicSite p j) _ (pinAt_mem_symbolicSite p k)
      (fun h => hk ((pinAt_first_inj p h).symm))
  obtain ⟨b,r,hb,hBM,hr,hD⟩ := exists_symbolic_margin p u m hm hu ha
  let l := (symbolicIndices p).map (Sum.inl : PinNumber p → SymbolIndex p)
  obtain ⟨s,a,hs,hsB,ha0,hN⟩ := exists_finite_normBound u l b hb
    (fun i => cutOn_mono930 (hu i) hBM)
  let L : ℚ := max 1 (max (p.radius : ℚ) a)
  have haL : a ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨s,hs,hsB.trans hBM,⟨⟨L,r,le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),hr,?_,hD.mono hsB⟩⟩⟩
  intro i
  have hI : (Sum.inl i : SymbolIndex p) ∈ l :=
    List.mem_map.mpr ⟨i,mem_symbolicIndices p i,rfl⟩
  exact distanceLe_mono (cutOn_mono930 (hu (.inl i)) (hsB.trans hBM))
    (ComplexBits.checked_cutOn 0 s) ha0 haL (hN (.inl i) hI)

noncomputable def IncomingGeometry.map (F : CompleteValueMap B C)
    (p : SymbolicTrace J) (site : J → ComplexBits B) (site' : J → ComplexBits C)
    (m : B) (G : IncomingGeometry p site m)
    (hS : ∀ j ∈ p.pins.map Prod.fst,(site j).map F = site' j) :
    IncomingGeometry p site' (F.toFun m) := by
  refine ⟨G.L,G.r,G.one_le,G.rad_le,G.positive,?_,?_⟩
  · intro i
    simpa only [map_distanceLe,ComplexBits.map_checked,hS _ (pinAt_mem_symbolicSite p i)]
      using F.monotone (G.norms i)
  · intro i
    obtain ⟨b,hb,hM⟩ := G.margin i
    refine ⟨b,hb,?_⟩
    let d := symbolicDenominator p i
    let H : J → ℕ → ComplexBits B := fun _ _ => ComplexBits.checked (0 : ℂ)
    let H' : J → ℕ → ComplexBits C := fun _ _ => ComplexBits.checked (0 : ℂ)
    have hMap : ((d.eval (symbolVal p site H)).map F) = d.eval (symbolVal p site' H') := by
      rw [Expr.eval_map]
      exact symbolicDenominator_eval_independent p i _ _ (fun j => hS _ (pinAt_mem_symbolicSite p j))
    have h : F.toFun m ≤ mapCut F (d.eval (symbolVal p site H)).normSq b := F.monotone hM
    rw [ComplexBits.map_normSq,hMap] at h
    exact h

def IncomingGeometry.mono (p : SymbolicTrace J) (site : J → ComplexBits B)
    {m s : B} (G : IncomingGeometry p site m) (h : s ≤ m) : IncomingGeometry p site s :=
  ⟨G.L,G.r,G.one_le,G.rad_le,G.positive,fun i => h.trans (G.norms i),G.margin.mono h⟩

end JSP000930.Negative
