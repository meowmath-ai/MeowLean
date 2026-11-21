import JSP000930SymbolicPrecision

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 700000 in
theorem exists_symbolic_refinement_on_pins (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J)
    (hSite : ∀ i ∈ p.pins,(site i).CutOn (⊤ : B))
    (hH : ∀ i ∈ p.pins,∀ n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i ∈ p.pins,∀ j ∈ p.pins,i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (m : B) (hm : m ≠ ⊥) (hP : m ≤ polyValid site H p) :
    ∃ (k : B) (s : SymbolicTrace J), k ≠ ⊥ ∧ k ≤ m ∧
      (decodeSymbolicTrace site H s).pins = p.pins ∧
      k ≤ (polynomialQ site H).refines (some (decodeSymbolicTrace site H s)) (some p) := by
  classical
  obtain ⟨a,log,ha,hAM,hList,hLog⟩ := valid_trace_select_pinned_log site H p m hm hP
  let base : SymbolicTrace J := ⟨[],log,p.radius,p.budget/2,by linarith [p.budget_pos],by
    rw [hList]
    exact p.pins.nodup_toList⟩
  have hPin (s : SymbolicTrace J) (hs : s.pins = log) (i : PinNumber s) :
      (pinAt s i).1 ∈ p.pins := by
    apply Finset.mem_toList.mp
    rw [← hList,← hs]
    exact List.mem_map.mpr ⟨pinAt s i,List.getElem_mem i.2,rfl⟩
  have hU (s : SymbolicTrace J) (hs : s.pins = log) (b : B) (i : SymbolIndex s) :
      (symbolVal s site H i).CutOn b := by
    rcases i with i|i
    · exact cutOn_mono930 (hSite _ (hPin s hs i)) le_top
    · exact cutOn_mono930 (hH _ (hPin s hs i) _) le_top
  have hApartAt (s : SymbolicTrace J) (hs : s.pins = log) (b : B) :
      ∀ i v,v ∈ symbolicOtherSites s i →
        b ≤ ((symbolVal s site H (.inl i)).name =ᴮ (symbolVal s site H v).name)ᶜ := by
    intro i v hv
    obtain ⟨j,hji,rfl⟩ := (mem_symbolicOtherSites s i v).mp hv
    exact le_top.trans (hApart _ (hPin s hs i) _ (hPin s hs j)
      (fun h => hji ((pinAt_first_inj s h).symm)))
  let u := symbolVal base site H
  obtain ⟨b,r,hb,hBA,hr,hMarg⟩ :=
    exists_symbolic_margin base u a ha (hU base rfl a) (hApartAt base rfl a)
  let P := (symbolicIndices base).map (Sum.inl : PinNumber base → SymbolIndex base)
  obtain ⟨c,M,hc,hCB,hM,hBound⟩ := exists_finite_normBound u P b hb (hU base rfl b)
  let L : ℚ := max 1 (max (p.radius : ℚ) M)
  have hL : 1 ≤ L := le_max_left _ _
  have hR : (p.radius : ℚ) ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hML : M ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hcM := hCB.trans (hBA.trans hAM)
  have hCoeff (d : B) (hd : d ≤ m) : ∀ v ∈ p.coeff,v.CutOn d :=
    (le_coeffValue_iff _ _).mp (hd.trans (hP.trans inf_le_left))
  obtain ⟨e,he,hBudget⟩ := exists_symbolic_precision L r (p.budget/2) hL hr
    (by linarith [p.budget_pos]) p.coeff.length base.pins.length
  obtain ⟨k,seed,hk,hKC,hSeed⟩ := exists_gaussian_seed p.coeff c hc (hCoeff c hcM) e he
  have hkM := hKC.trans hcM
  have hkA := hKC.trans (hCB.trans hBA)
  let s : SymbolicTrace J := { base with seed := seed }
  let q := decodeSymbolicTrace site H s
  let w := symbolVal s site H
  let η : ℚ := e*(1+L)^p.coeff.length
  let Δ : ℚ := (s.pins.length : ℚ)*(η/r*(L+L)^s.pins.length)
  have hη : 0 ≤ η := mul_nonneg he.le (pow_nonneg (by linarith) _)
  have hΔ : 0 ≤ Δ := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (div_nonneg hη hr.le) (pow_nonneg (by linarith) _))
  have hSamePins : q.pins = p.pins := by
    change (log.map Prod.fst).toFinset = p.pins
    rw [hList,Finset.toList_toFinset]
  have hW : ∀ i,(w i).CutOn k := hU s rfl k
  have hApartW := hApartAt s rfl k
  have hV := symbolicTrace_valid_from_environment site H s k hW hApartW
  have hMargin : SymbolicMargin s w k r := by
    intro i
    obtain ⟨q,hq,hqB⟩ := hMarg i
    have hDen : symbolicDenominator s i = symbolicDenominator base i := by
      with_unfolding_all rfl
    rw [hDen]
    have hw : w = u := by
      funext i
      cases i <;> rfl
    rw [hw]
    exact ⟨q,hq,hKC.trans (hCB.trans hqB)⟩
  have hSmall (i : PinNumber s) :
      k ≤ distanceLe (w (.inl i)) (ComplexBits.checked (0 : ℂ)) L := by
    have hi : (Sum.inl i : SymbolIndex base) ∈ P :=
      List.mem_map.mpr ⟨i,mem_symbolicIndices base i,rfl⟩
    exact distanceLe_mono (hW (.inl i)) (ComplexBits.checked_cutOn 0 k) hM hML
      (hKC.trans (hBound (.inl i) hi))
  let vSeed : List (ComplexBits B) := seed.map (fun a => ComplexBits.checked (gaussianRat a))
  have hv (v : ComplexBits B) (hv : v ∈ vSeed) : v.CutOn k := by
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hv
    exact ComplexBits.checked_cutOn _ k
  have hNear (i : PinNumber s) : k ≤ distanceLe (w (.inr i))
      ((symbolicAtPinSeed s i).eval w) η := by
    let z := w (.inl i)
    let f := p.eval z
    let t := mixedPolynomialEval vSeed z
    have hF : f.CutOn k := mixedPolynomialEval_cutOn p.coeff z (hCoeff k hkM) (hW (.inl i))
    have hT : t.CutOn k := mixedPolynomialEval_cutOn vSeed z hv (hW (.inl i))
    have hEq : k ≤ f.name =ᴮ (w (.inr i)).name :=
      hkA.trans (hLog (pinAt s i) (List.getElem_mem i.2))
    have hSeedF : k ≤ distanceLe f t η :=
      seedClose_horner_bound k z (hW (.inl i)) e L he.le (zero_le_one.trans hL)
        (hSmall i) p.coeff seed (hCoeff k hkM) hSeed
    have h := extend_same_mark_seed_error hF (hW (.inr i)) hT hEq hη hSeedF
    simpa only [t,vSeed,z,symbolicAtPinSeed,atExpr_eval,seedExpr,mixedPolynomialEval_map_seed,Expr.eval]
      using h
  refine ⟨k,s,hk,hkM,hSamePins,?_⟩
  change k ≤ (polyValid site H q ⊓ polyValid site H p) ⊓ refinesValue site q p
  refine le_inf (le_inf hV (hkM.trans hP)) ?_
  unfold refinesValue
  refine le_inf ?_ (le_inf ?_ ?_)
  · have hCr : p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧ p.radius ≤ q.radius := by
      refine ⟨?_,?_,le_rfl⟩
      · rw [hSamePins] <;> exact fun _ hi => hi
      · change p.budget/2 ≤ p.budget
        linarith [p.budget_pos]
    simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hCr,le_top]
  · unfold agreementValue
    apply le_iInf
    intro j
    have hJ : j.1 ∈ (log.map Prod.fst).toFinset := by
      rw [hList,Finset.toList_toFinset]
      exact j.2
    obtain ⟨v,hvLog,hvJ⟩ := List.mem_map.mp (List.mem_toFinset.mp hJ)
    obtain ⟨i,hi,hvi⟩ := List.getElem_of_mem hvLog
    let idx : PinNumber s := ⟨i,hi⟩
    have hIdx : pinAt s idx = v := hvi
    have hp := symbolic_log_named_pin s k w idx hW hApartW
    change k ≤ (q.eval (site (pinAt s idx).1)).name =ᴮ (H (pinAt s idx).1 (pinAt s idx).2).name at hp
    rw [hIdx,hvJ] at hp
    have hp' := hkA.trans (hLog v hvLog)
    rw [hvJ] at hp'
    exact (le_inf hp (hp'.trans_eq bSet.bv_eq_symm)).trans bSet.bv_eq_trans
  · unfold discValue
    apply le_iInf
    intro g
    let z := ComplexBits.checked (B := B) (gridPoint g)
    let f := p.eval z
    let t := mixedPolynomialEval vSeed z
    have hz : z.CutOn k := ComplexBits.checked_cutOn _ k
    have hF : f.CutOn k := mixedPolynomialEval_cutOn p.coeff z (hCoeff k hkM) hz
    have hT : t.CutOn k := mixedPolynomialEval_cutOn vSeed z hv hz
    have hQ : (q.eval z).CutOn k := eval_cutOn_of_coeff (hV.trans inf_le_left) hz
    have hZ : k ≤ distanceLe z (ComplexBits.checked (0 : ℂ)) L := by
      apply checked_distanceLe
      rw [dist_zero_right]
      exact (gridPoint_norm_le g).trans (by exact_mod_cast hR)
    have hTail : k ≤ distanceLe t f η :=
      distanceLe_symm_mono hF hT hη le_rfl
        (seedClose_horner_bound k z hz e L he.le (zero_le_one.trans hL)
          hZ p.coeff seed (hCoeff k hkM) hSeed)
    have hDrift : k ≤ distanceLe (q.eval z) t Δ :=
      symbolic_named_grid_displacement s w k g L η r hL hR hη hr hW hApartW hSmall hNear hMargin
    have hE : Δ + η ≤ p.budget - q.budget := by
      change Δ + η ≤ p.budget - p.budget/2
      rw [show p.budget-p.budget/2 = p.budget/2 by ring]
      exact hBudget
    exact distanceLe_mono hQ hF (add_nonneg hΔ hη) hE
      (distanceLe_triangle hQ hT hF hΔ hη hDrift hTail)

theorem exists_symbolic_refinement (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B)) (hH : ∀ i n,(H i n).CutOn (⊤ : B))
    (hApart : ∀ i j : J,i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (p : PolyTrace B J) (m : B) (hm : m ≠ ⊥) (hP : m ≤ polyValid site H p) :
    ∃ (k : B) (s : SymbolicTrace J), k ≠ ⊥ ∧ k ≤ m ∧
      (decodeSymbolicTrace site H s).pins = p.pins ∧
      k ≤ (polynomialQ site H).refines (some (decodeSymbolicTrace site H s)) (some p) :=
  exists_symbolic_refinement_on_pins site H p (fun i _ => hSite i)
    (fun i _ n => hH i n) (fun i _ j _ h => hApart i j h) m hm hP

end JSP000930.Negative
