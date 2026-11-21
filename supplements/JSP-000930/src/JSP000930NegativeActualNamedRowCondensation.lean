import JSP000930NegativeGenuineSameBinSplice

open bSet Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanNames
  JSP000933.CantorCodes

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem namedSpliceCellData_mono (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (z : J) (p a : Option (PolyTrace B J)) (k : SpliceBin) {m s : B}
    (h : NamedSpliceCellData site H z p a k m) (hs : s ≤ m) :
    NamedSpliceCellData site H z p a k s := by
  cases k with
  | none => exact h
  | some key =>
    rcases key with ⟨i,R,E,L,seed⟩
    cases p with
    | none => exact h
    | some p =>
      obtain ⟨G,hL,hR,hE,hz,ha,hVal,hNear⟩ := h
      exact ⟨G.mono hs,hL,hR,hE,hz,ha,hs.trans hVal,fun t => hs.trans (hNear t)⟩

noncomputable def namedSpliceCell
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (k : SpliceBin) (p : SupportedNamedRow B J (fun j => A j ∨ j = z))
    (a : SupportedNamedRow B J A) : B :=
  ⨆ s : {m : B // m ≤ (polynomialQ site H).valid p.val ∧
    m ≤ (polynomialQ site H).valid a.val ∧ NamedSpliceCellData site H z p.val a.val k m},s.val

theorem namedSpliceCell_splice
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (k : SpliceBin) (p q : SupportedNamedRow B J (fun j => A j ∨ j = z))
    (a b : SupportedNamedRow B J A) :
    ((namedSpliceCell site H A z k p a ⊓ namedSpliceCell site H A z k q b) ⊓
      commonRefinementValue (supportedNamedRowQ site H A) a b) ≤
      commonRefinementValue (supportedNamedRowQ site H (fun j => A j ∨ j = z)) p q := by
  unfold namedSpliceCell
  simp only [commonRefinementValue,iSup_inf_eq,inf_iSup_eq]
  apply iSup_le
  intro h
  apply iSup_le
  intro t
  apply iSup_le
  intro s
  let m : B := (s.val ⊓ t.val) ⊓ ((supportedNamedRowQ site H A).refines h a ⊓
    (supportedNamedRowQ site H A).refines h b)
  change m ≤ _
  by_cases hm : m = ⊥
  · simp [hm]
  have hs : m ≤ s.val := inf_le_left.trans inf_le_left
  have ht : m ≤ t.val := inf_le_left.trans inf_le_right
  obtain ⟨r,hrp,hrq⟩ := namedSpliceCell_compatible site H A z hSite p q a b h k m hm
    (hs.trans s.property.1) (ht.trans t.property.1)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    (namedSpliceCellData_mono site H z _ _ k s.property.2.2 hs)
    (namedSpliceCellData_mono site H z _ _ k t.property.2.2 ht)
  exact le_iSup_of_le r (le_inf hrp hrq)

noncomputable def namedRow_spliceCondensation
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (A : J → Prop) (z : J)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hApart : ∀ i j,(A i ∨ i = z) → (A j ∨ j = z) → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ) :
    SpliceCondensation (supportedNamedRowQ site H A)
      (supportedNamedRowQ site H (fun j => A j ∨ j = z)) := by
  classical
  letI : Encodable SpliceBin := Encodable.ofCountable SpliceBin
  let C (n : ℕ) (p : SupportedNamedRow B J (fun j => A j ∨ j = z))
      (a : SupportedNamedRow B J A) : B :=
    (Encodable.decode (α := SpliceBin) n).elim ⊥ (fun k => namedSpliceCell site H A z k p a)
  refine ⟨C,?_,?_,?_⟩
  · intro p
    let D := ⨆ n : ℕ,⨆ a : SupportedNamedRow B J A,C n p a
    change (polynomialQ site H).valid p.val ≤ D
    by_contra hn
    let m := (polynomialQ site H).valid p.val ⊓ Dᶜ
    have hm : m ≠ ⊥ := fun he => hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨s,k,a,hs,hSM,hA,hCert⟩ := namedSpliceCell_exists_on site H A z hSite hApart p m hm inf_le_left
    have hsC : s ≤ C (Encodable.encode k) p a := by
      simp only [C,Encodable.encodek,Option.elim_some]
      exact le_iSup_of_le ⟨s,hSM.trans inf_le_left,hA,hCert⟩ le_rfl
    have hsD : s ≤ D := hsC.trans (le_iSup_of_le (Encodable.encode k) (le_iSup _ a))
    exact hs (disjoint_compl_right.out _ hsD (hSM.trans inf_le_right))
  · intro n p a
    unfold C
    cases Encodable.decode (α := SpliceBin) n with
    | none => exact bot_le
    | some k => exact iSup_le fun s => s.property.2.1
  · intro n p q a b
    unfold C
    cases Encodable.decode (α := SpliceBin) n with
    | none => simp
    | some k => exact namedSpliceCell_splice site H A z hSite k p q a b

end JSP000930.Negative
