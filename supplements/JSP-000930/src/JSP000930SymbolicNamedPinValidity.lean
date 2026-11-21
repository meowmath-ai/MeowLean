import JSP000930SymbolicLagrangeGround

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem safe_atom_p83 {V : Type} (u : V → ComplexBits B) (m : B) (i : V) :
    (Expr.atom i).Safe u m := by
  intro a ha
  exact (List.not_mem_nil ha).elim

theorem seedExpr_safe (p : SymbolicTrace J) (u : SymbolIndex p → ComplexBits B) (m : B) :
    CoeffSafe u m (seedExpr p) := by
  intro a ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  intro d hd
  exact (List.not_mem_nil hd).elim

theorem symbolicVanish_safe (p : SymbolicTrace J)
    (u : SymbolIndex p → ComplexBits B) (m : B) (i : PinNumber p) :
    CoeffSafe u m (symbolicVanish p i) := by
  apply coeffSafe_vanishing
  intro a ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
  exact safe_atom_p83 u m s

theorem symbolicCorrection_safe (p : SymbolicTrace J) (m : B)
    (u : SymbolIndex p → ComplexBits B) (i : PinNumber p)
    (hu : ∀ j,(u j).CutOn m)
    (hApart : ∀ a ∈ symbolicOtherSites p i,
      m ≤ ((u (Sum.inl i)).name =ᴮ (u a).name)ᶜ) :
    CoeffSafe u m (symbolicCorrection p i) := by
  haveI : Nonempty (SymbolIndex p) := ⟨Sum.inl i⟩
  have hn := named_vanishing_positive u (Sum.inl i) (symbolicOtherSites p i) m hu hApart
  have hV := symbolicVanish_safe p u m i
  have hJ := safe_atom_p83 u m (Sum.inl i)
  have hY := safe_atom_p83 u m (Sum.inr i)
  exact coeffSafe_scale
    (safe_mul (safe_add hY (safe_neg (atExpr_safe (seedExpr_safe p u m) hJ)))
      (safe_inv (atExpr_safe hV hJ) hn)) hV

theorem symbolicCoefficients_safe (p : SymbolicTrace J) (m : B)
    (u : SymbolIndex p → ComplexBits B) (hu : ∀ j,(u j).CutOn m)
    (hApart : ∀ i a, a ∈ symbolicOtherSites p i →
      m ≤ ((u (Sum.inl i)).name =ᴮ (u a).name)ᶜ) :
    CoeffSafe u m (symbolicCoefficients p) := by
  have hN (l : List (PinNumber p)) : CoeffSafe u m
      (l.foldr (fun i a => plus (symbolicCorrection p i) a) []) := by
    induction l with
    | nil =>
      intro a ha
      exact (List.not_mem_nil ha).elim
    | cons i l ih =>
      exact coeffSafe_plus (symbolicCorrection_safe p m u i hu (hApart i)) ih
  exact coeffSafe_plus (seedExpr_safe p u m) (hN (symbolicIndices p))

theorem symbolicLog_nameApart (p : SymbolicTrace J) (m : B)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (h : ∀ i j : J, i ≠ j → m ≤ ((site i).name =ᴮ (site j).name)ᶜ) :
    ∀ i a, a ∈ symbolicOtherSites p i →
      m ≤ (((symbolVal p site H) (Sum.inl i)).name =ᴮ ((symbolVal p site H) a).name)ᶜ := by
  intro i a ha
  obtain ⟨j,hji,rfl⟩ := (mem_symbolicOtherSites p i a).mp ha
  exact h _ _ (fun he => hji ((pinAt_first_inj p he).symm))

theorem symbolic_log_named_pin (p : SymbolicTrace J) (m : B)
    (u : SymbolIndex p → ComplexBits B) (i : PinNumber p)
    (hu : ∀ j,(u j).CutOn m)
    (hApart : ∀ i a, a ∈ symbolicOtherSites p i →
      m ≤ ((u (Sum.inl i)).name =ᴮ (u a).name)ᶜ) :
    m ≤ (mixedPolynomialEval ((symbolicCoefficients p).map (Expr.eval u))
      (u (Sum.inl i))).name =ᴮ (u (Sum.inr i)).name := by
  haveI : Nonempty (SymbolIndex p) := ⟨Sum.inl i⟩
  have hSafe := symbolicCoefficients_safe p m u hu hApart
  have h := forced_eq_of_apart_sites u (Sum.inl i) (symbolicOtherSites p i) m
    (atExpr (symbolicCoefficients p) (.atom (Sum.inl i))) (.atom (Sum.inr i)) hu
    (atExpr_safe hSafe (safe_atom_p83 u m (Sum.inl i)))
    (safe_atom_p83 u m (Sum.inr i)) (hApart i) (symbolic_ground_pin p i)
  simpa only [atExpr_eval,Expr.eval] using h

theorem symbolicTrace_valid_from_environment
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (m : B)
    (hu : ∀ j, (symbolVal p site H j).CutOn m)
    (hNe : ∀ i a, a ∈ symbolicOtherSites p i →
      m ≤ (((symbolVal p site H) (.inl i)).name =ᴮ ((symbolVal p site H) a).name)ᶜ) :
    m ≤ polyValid site H (decodeSymbolicTrace site H p) := by
  classical
  let u := symbolVal p site H
  have hSafe := symbolicCoefficients_safe p m u hu hNe
  refine le_inf ((le_coeffValue_iff _ _).mpr ?_) ?_
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact a.eval_cutOn u m hu (hSafe a ha)
  · unfold paletteValue
    apply le_iInf
    intro j
    have hj : j.1 ∈ (p.pins.map Prod.fst).toFinset := j.2
    obtain ⟨a,ha,ha'⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    obtain ⟨i,hi,hig⟩ := List.getElem_of_mem ha
    let k : PinNumber p := ⟨i,hi⟩
    have hk : pinAt p k = a := hig
    have hp := symbolic_log_named_pin p m u k hu hNe
    change m ≤ ((decodeSymbolicTrace site H p).eval (site (pinAt p k).1)).name =ᴮ
      (H (pinAt p k).1 (pinAt p k).2).name at hp
    rw [hk,ha'] at hp
    exact le_iSup_of_le a.2 hp
theorem symbolicTrace_valid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (m : B)
    (hSite : ∀ i,(site i).CutOn m) (hH : ∀ i n,(H i n).CutOn m)
    (hApart : ∀ i j : J, i ≠ j → m ≤ ((site i).name =ᴮ (site j).name)ᶜ) :
    m ≤ polyValid site H (decodeSymbolicTrace site H p) := by
  apply symbolicTrace_valid_from_environment site H p m _ (symbolicLog_nameApart p m site H hApart)
  rintro (i|i)
  · exact hSite _
  · exact hH _ _

end JSP000930.Negative
