import JSP000930SymbolicDisplacementGround

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def symbolicDenominator (p : SymbolicTrace J) (i : PinNumber p) : Expr (SymbolIndex p) :=
  atExpr (symbolicVanish p i) (.atom (.inl i))

def symbolicAtPinSeed (p : SymbolicTrace J) (i : PinNumber p) : Expr (SymbolIndex p) :=
  atExpr (seedExpr p) (.atom (.inl i))

def SymbolicMargin (p : SymbolicTrace J) (u : SymbolIndex p → ComplexBits B)
    (m : B) (r : ℚ) : Prop :=
  ∀ i : PinNumber p, ∃ b : RatPresentation,
    r^2 ≤ b.value ∧ m ≤ ((symbolicDenominator p i).eval u).normSq b

theorem SymbolicMargin.mono {p : SymbolicTrace J} {u : SymbolIndex p → ComplexBits B}
    {m s : B} {r : ℚ} (h : SymbolicMargin p u m r) (hs : s ≤ m) :
    SymbolicMargin p u s r := by
  intro i
  obtain ⟨b,hb,hm⟩ := h i
  exact ⟨b,hb,hs.trans hm⟩

private theorem finite_common_rat_bound_p93 {I : Type} [Fintype I] (f : I → ℚ)
    (hf : ∀ i,0 < f i) : ∃ r : ℚ, 0 < r ∧ r ≤ 1 ∧ ∀ i,r ≤ f i := by
  classical
  have hA (s : Finset I) : ∃ r : ℚ,0 < r ∧ r ≤ 1 ∧ ∀ i ∈ s,r ≤ f i := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1,zero_lt_one,le_rfl,?_⟩
      intro i hi
      simp at hi
    | @insert i s hi ih =>
      obtain ⟨r,hr,hr1,hrS⟩ := ih
      refine ⟨min r (f i),lt_min hr (hf i),(min_le_left _ _).trans hr1,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hrS j hj)
  obtain ⟨r,hr,hr1,h⟩ := hA Finset.univ
  exact ⟨r,hr,hr1,fun i => h i (Finset.mem_univ i)⟩

theorem exists_symbolic_margin (p : SymbolicTrace J) (u : SymbolIndex p → ComplexBits B)
    (m : B) (hm : m ≠ ⊥) (hu : ∀ a,(u a).CutOn m)
    (hApart : ∀ i a,a ∈ symbolicOtherSites p i → m ≤ ((u (.inl i)).name =ᴮ (u a).name)ᶜ) :
    ∃ (s : B) (r : ℚ),s ≠ ⊥ ∧ s ≤ m ∧ 0 < r ∧ SymbolicMargin p u s r := by
  classical
  let l := (symbolicIndices p).map (symbolicDenominator p)
  have hPos : ∀ d ∈ l,m ≤ positiveCutValue (d.eval u).normSq := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
    haveI : Nonempty (SymbolIndex p) := ⟨.inl i⟩
    exact named_vanishing_positive u (.inl i) (symbolicOtherSites p i) m hu (hApart i)
  obtain ⟨s,hs,hsM,hS⟩ := exists_fixedMargins u l m hm hPos
  have hi (i : PinNumber p) : ∃ b : RatPresentation,
      0 < b.value ∧ s ≤ ((symbolicDenominator p i).eval u).normSq b :=
    hS _ (List.mem_map.mpr ⟨i,mem_symbolicIndices p i,rfl⟩)
  choose b hb hbS using hi
  obtain ⟨r,hr,hr1,hrB⟩ := finite_common_rat_bound_p93 (fun i => (b i).value) hb
  have hr2 : r^2 ≤ r := by
    rw [pow_two]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 hr.le
  exact ⟨s,r,hs,hsM,hr,fun i => ⟨b i,hr2.trans (hrB i),hbS i⟩⟩

end JSP000930.Negative
