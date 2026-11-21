import JSP000930NegativeNativeDistinguishedCoordinate

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000930.BooleanAnalysis

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B]

private def supportLabelCongr {A Z : J → Prop} (h : ∀ j,A j ↔ Z j) :
    SupportedSymbolic J A ≃ SupportedSymbolic J Z where
  toFun := includeNamedSupport (fun j => (h j).mp)
  invFun := includeNamedSupport (fun j => (h j).mpr)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem symbolicRowProduct_oneFibre_at
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (A Z : I → J → Prop) (k : I) (z : J)
    (hNew : ∀ j,(A k j ∨ j = z) ↔ Z k j)
    (hKeep : ∀ i,i ≠ k → ∀ j,A i j ↔ Z i j)
    (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i j n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ i j,Z k i → Z k j → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (A i)))) :
    ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (Z i))) := by
  let K := {i : I // i ≠ k}
  let R (i : K) := supportedSymbolicQ site (H i.val) (A i.val)
  let P := pointedRowFamily (supportedSymbolicQ site (H k) (fun j => A k j ∨ j = z)) R
  let Q (i : I) := supportedSymbolicQ site (H i) (Z i)
  let e := distinguishRowIndex k
  let f (i : Unit ⊕ K) : PointedRows (SupportedSymbolic J (fun j => A k j ∨ j = z))
      (fun i : K => SupportedSymbolic J (A i.val)) i ≃ SupportedSymbolic J (Z (e i)) :=
    match i with
    | .inl _ => supportLabelCongr hNew
    | .inr a => supportLabelCongr (hKeep a.val a.property)
  let F := rowProductQ_equivLabels P Q e f
    (fun j => by cases j <;> exact fun _ => rfl)
    (fun j => by cases j <;> exact fun _ _ => rfl)
  apply (F.relativeCCC_iff hB).mp
  let E₀ := rowProductQ_distinguish (fun i => supportedSymbolicQ site (H i) (A i)) k
  have h₀ := (E₀.relativeCCC_iff hB).mpr hOld
  exact supportedSymbolic_one_fibre_nativeRowProduct_relativeCCC R site (H k) (A k) z
    hB hSite (hH k)
    (fun i j hi hj => hApart i j ((hNew i).mp hi) ((hNew j).mp hj)) h₀

theorem symbolicRowProduct_countableFibres_relativeCCC [Fintype I]
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (A : ℕ → I → J → Prop) (Z : I → J → Prop)
    (eventRow : ℕ → I) (eventSite : ℕ → J)
    (hChange : ∀ n j,(A n (eventRow n) j ∨ j = eventSite n) ↔ A (n+1) (eventRow n) j)
    (hKeep : ∀ n i,i ≠ eventRow n → ∀ j,A n i j ↔ A (n+1) i j)
    (hInto : ∀ n i j,A n i j → Z i j)
    (hCover : ∀ i j,Z i j → ∃ n,A n i j)
    (hB : BoundsCountableOmegaOneNames B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hH : ∀ i j n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ row i j,Z row i → Z row j → i ≠ j →
      (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hOld : ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (A 0 i)))) :
    ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (Z i))) := by
  have hSucc (n : ℕ) (i : I) (j : J) (h : A n i j) : A (n+1) i j := by
    by_cases he : i = eventRow n
    · subst i
      exact (hChange n j).mp (Or.inl h)
    · exact (hKeep n i he j).mp h
  have hMono (n m : ℕ) (hle : n ≤ m) (i : I) (j : J) (h : A n i j) : A m i j := by
    induction m,hle using Nat.le_induction with
    | base => exact h
    | succ m _ ih => exact hSucc m i j ih
  apply symbolicRowProduct_natExpansion_relativeCCC site H A Z hB hMono hInto hCover
  intro n
  induction n with
  | zero => exact hOld
  | succ n ih =>
    exact symbolicRowProduct_oneFibre_at site H (A n) (A (n+1))
      (eventRow n) (eventSite n) (hChange n) (hKeep n) hB hSite hH
      (fun i j hi hj => hApart (eventRow n) i j
        (hInto (n+1) _ i hi) (hInto (n+1) _ j hj)) ih

end JSP000930.Negative
