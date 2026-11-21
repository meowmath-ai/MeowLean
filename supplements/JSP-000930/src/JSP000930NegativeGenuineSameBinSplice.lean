import JSP000930NegativeActualNamedCellCoverage

open bSet Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem guard_bound_of_radius_eq {site : J → ComplexBits B} {z : J} {l : List J}
    {m : B} {R R' : ℕ} (h : R = R') (G : NamedSpliceGuard site z l R m) :
    (show NamedSpliceGuard site z l R' m from h ▸ G).bound = G.bound := by
  cases h
  rfl

private theorem supportedNamedRow_widen {A : J → Prop} {z : J}
    (p : SupportedNamedRow B J A) : NamedRowAt (fun j => A j ∨ j = z) p.val :=
  fun j hj => Or.inl (p.property j hj)

theorem namedSpliceCell_compatible
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (p q : SupportedNamedRow B J (fun j => A j ∨ j = z))
    (a b h : SupportedNamedRow B J A) (k : SpliceBin) (m : B) (hm : m ≠ ⊥)
    (hP : m ≤ (polynomialQ site H).valid p.val)
    (hQ : m ≤ (polynomialQ site H).valid q.val)
    (hA : m ≤ (polynomialQ site H).refines h.val a.val)
    (hB : m ≤ (polynomialQ site H).refines h.val b.val)
    (hp : NamedSpliceCellData site H z p.val a.val k m)
    (hq : NamedSpliceCellData site H z q.val b.val k m) :
    ∃ r : SupportedNamedRow B J (fun j => A j ∨ j = z),
      m ≤ (polynomialQ site H).refines r.val p.val ∧
      m ≤ (polynomialQ site H).refines r.val q.val := by
  cases k with
  | none =>
    change a.val = p.val at hp
    change b.val = q.val at hq
    rw [hp] at hA
    rw [hq] at hB
    exact ⟨⟨h.val,supportedNamedRow_widen h⟩,hA,hB⟩
  | some key =>
    rcases key with ⟨i,R,E,L,seed⟩
    rcases p with ⟨_ | p,hpA⟩
    · exact False.elim hp
    rcases q with ⟨_ | q,hqA⟩
    · exact False.elim hq
    obtain ⟨G₀,hL₀,hR₀,hE₀,_,ha,hValue₀,hClose₀⟩ := hp
    obtain ⟨G₁,hL₁,hR₁,hE₁,_,hb,hValue₁,hClose₁⟩ := hq
    have hR : q.radius = p.radius := hR₁.symm.trans hR₀
    have hE : q.budget = p.budget := hE₁.symm.trans hE₀
    have hG : G₁.bound = G₀.bound := hL₁.trans hL₀.symm
    have hSame : m ≤ (p.eval (site z)).name =ᴮ (q.eval (site z)).name :=
      bv_trans hValue₀ (bv_symm hValue₁)
    rcases h with ⟨_ | h,hhA⟩
    · rw [ha] at hA
      exact False.elim (hm (le_bot_iff.mp hA))
    rw [ha] at hA
    rw [hb] at hB
    obtain ⟨hOld₀,hTight⟩ := erased_of_tight_refinement site H p h z G₀.bound G₀.bound_one hm hA
    obtain ⟨hOld₁,_⟩ := erased_of_tight_refinement site H q h z G₁.bound G₁.bound_one hm hB
    have hD (t : RatGrid p.radius) :
        m ≤ distanceLe (p.eval (ComplexBits.checked (gridPoint t)))
          (q.eval (ComplexBits.checked (gridPoint t))) (p.budget/4) := by
      let t' : RatGrid q.radius := ⟨t.val,by simpa only [hR] using t.property⟩
      let x := ComplexBits.checked (B := B) (gridPoint t)
      have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
      have h₀ := eval_cutOn_of_coeff (p := p) (hP.trans inf_le_left) hx
      have h₁ := eval_cutOn_of_coeff (p := q) (hQ.trans inf_le_left) hx
      have hSeed := spliceSeedEval_cut seed x hx
      have hh : m ≤ distanceLe (q.eval x) (spliceSeedEval seed x) (p.budget/8) := by
        rw [← hE]
        exact hClose₁ t'
      have he : 0 ≤ p.budget/8 := div_nonneg p.budget_pos.le (by norm_num)
      have h := distanceLe_triangle h₀ hSeed h₁ he he (hClose₀ t)
        (distanceLe_splice_symm h₁ hSeed he hh)
      rwa [show p.budget/8+p.budget/8 = p.budget/4 by ring] at h
    let e := p.budget/(4*G₀.bound)
    have he : 0 ≤ e := div_nonneg p.budget_pos.le
      (mul_nonneg (by norm_num) (zero_le_one.trans G₀.bound_one))
    have hQuant : G₁.bound*e + p.budget/4 ≤ p.budget - p.budget/2 := by
      rw [hG]
      exact namedSplice_quarter_budget _ _ _ _ p.budget_pos G₀.bound_one le_rfl le_rfl
    let hGuard : NamedSpliceGuard site z (eraseSplicePin q z).pins.toList p.radius m :=
      hR ▸ G₁
    obtain ⟨r,hPins,_,_,hRP,hRQ⟩ := named_splice_common_refinement site H p q h z m
      (fun i => cutOn_mono930 (hSite i) le_top) hP hQ hOld₀ hOld₁ hSame hR hE
      hGuard e (p.budget/4) (p.budget/2) he
      (div_nonneg p.budget_pos.le (by norm_num)) (div_pos p.budget_pos (by norm_num)) (by
        have hg : hGuard.bound = G₁.bound := guard_bound_of_radius_eq hR G₁
        rw [hg]
        exact hQuant) hTight hD
    refine ⟨⟨some r,?_⟩,hRP,hRQ⟩
    intro j hj
    change j ∈ r.pins at hj
    rw [hPins,Finset.mem_union] at hj
    exact hj.elim (hpA j) (hqA j)

end JSP000930.Negative
