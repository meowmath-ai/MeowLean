import JSP000930NegativeSupportedNamedRowTightening

open bSet Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.CantorCodes
  JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def NamedSpliceCellData (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (z : J) (p a : Option (PolyTrace B J)) (k : SpliceBin) (m : B) : Prop :=
  match k,p with
  | none,_ => a = p
  | some (index,R,E,L,seed), some x =>
      ∃ g : NamedSpliceGuard site z (eraseSplicePin x z).pins.toList x.radius m,
        g.bound = L ∧ R = x.radius ∧ E = x.budget ∧ z ∈ x.pins ∧
        a = some (tightErasedSplice x z g.bound g.bound_one) ∧
        m ≤ ((x.eval (site z)).name =ᴮ (H z index).name) ∧
        ∀ t : RatGrid x.radius,m ≤ distanceLe (x.eval (ComplexBits.checked (gridPoint t)))
          (spliceSeedEval seed (ComplexBits.checked (gridPoint t))) (x.budget/8)
  | some _,none => False

theorem namedSpliceCell_exists_on
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (p : SupportedNamedRow B J (fun j => A j ∨ j = z)) (m : B) (hm : m ≠ ⊥)
    (hP : m ≤ (polynomialQ site H).valid p.val) :
    ∃ (s : B) (k : SpliceBin) (a : SupportedNamedRow B J A),
      s ≠ ⊥ ∧ s ≤ m ∧ s ≤ (polynomialQ site H).valid a.val ∧
      NamedSpliceCellData site H z p.val a.val k s := by
  rcases p with ⟨_ | x,hp⟩
  · exact ⟨m,none,⟨none,by simp [NamedRowAt,polyLabelPins]⟩,hm,le_rfl,le_top,rfl⟩
  by_cases hx : z ∈ x.pins
  · have hPalette : m ≤ ⨆ i : ℕ,(x.eval (site z)).name =ᴮ (H z i).name :=
      (hP.trans inf_le_right).trans (iInf_le _ (⟨z,hx⟩ : {j : J // j ∈ x.pins}))
    obtain ⟨i,s,hs,hsm,hVal⟩ := exists_nonzero_below_choice_r135 m hm _ hPalette
    obtain ⟨t,ht,hts,⟨G⟩⟩ := exists_named_splice_guard site z
      (eraseSplicePin x z).pins.toList x.radius s hs
      (fun j => cutOn_mono930 (hSite j) le_top) (by
        intro j hj
        obtain ⟨hne,hjp⟩ := Finset.mem_erase.mp (Finset.mem_toList.mp hj)
        exact le_top.trans (hApart z j (Or.inr rfl) (hp j hjp) hne.symm))
    have htm := hts.trans hsm
    have hCoeff : ∀ a ∈ x.coeff,a.CutOn t :=
      (le_coeffValue_iff _ _).mp (htm.trans (hP.trans inf_le_left))
    obtain ⟨b,seed,hb,hbt,hClose⟩ := exists_splice_center_bin x t ht hCoeff
    let G' := G.mono hbt
    let a : SupportedNamedRow B J A :=
      ⟨some (tightErasedSplice x z G'.bound G'.bound_one),erase_mem_old hp⟩
    have hbm := hbt.trans htm
    refine ⟨b,some (i,x.radius,x.budget,G'.bound,seed),a,hb,hbm,?_,?_⟩
    · exact (hbm.trans hP).trans (tightErasedSplice_valid site H x z G'.bound G'.bound_one)
    · exact ⟨G',rfl,rfl,rfl,hx,rfl,hbt.trans (hts.trans hVal),hClose⟩
  · have hOld : NamedRowAt A (some x) := by
      intro j hj
      refine (hp j hj).resolve_right ?_
      exact fun he => hx (he ▸ hj)
    exact ⟨m,none,⟨some x,hOld⟩,hm,le_rfl,hP,rfl⟩

end JSP000930.Negative
