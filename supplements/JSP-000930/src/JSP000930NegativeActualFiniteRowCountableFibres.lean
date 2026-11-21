import JSP000930NegativeCountableSupportedRowUnion
import JSP000930AnalyticFiniteSupportCutoff

open Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000930.BooleanAnalysis

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

def includeNamedSupport {A Z : J → Prop} (h : ∀ j,A j → Z j)
    (p : SupportedSymbolic J A) : SupportedSymbolic J Z := by
  refine ⟨p.val,?_⟩
  have hp := p.property
  cases hp0 : p.val with
  | none => exact True.intro
  | some q =>
    have hq : SymbolicLabelAt A (some q) := hp0 ▸ p.property
    exact fun j hj => h j (hq j hj)

theorem dependentFiniteRows_have_natStage
    (A : ℕ → I → J → Prop) (Z : I → J → Prop)
    (hMono : ∀ n m,n ≤ m → ∀ i j,A n i j → A m i j)
    (hCover : ∀ i j,Z i j → ∃ n,A n i j)
    (p : ∀ i,SupportedSymbolic J (Z i)) :
    ∃ n,∀ i,SymbolicLabelAt (A n i) (p i).val := by
  classical
  let pins (i : I) : Finset J :=
    match (p i).val with
    | none => ∅
    | some q => (q.pins.map Prod.fst).toFinset
  let P : Finset (I × J) := Finset.univ.biUnion
    (fun i => (pins i).image (fun j => (i,j)))
  have hz (ij : I × J) (h : ij ∈ P) : Z ij.1 ij.2 := by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨j,hij,rfl⟩ := Finset.mem_image.mp hi
    have hp := (p i).property
    cases he : (p i).val with
    | none => simp [pins,he] at hij
    | some q =>
      rw [he] at hp
      exact hp j (List.mem_toFinset.mp (by simpa only [pins,he] using hij))
  obtain ⟨n,hn⟩ := finite_support_has_stage (fun n (ij : I × J) => A n ij.1 ij.2)
    (fun ij => Z ij.1 ij.2) (fun h i => hMono _ _ h i.1 i.2)
    (fun a b => ⟨max a b,le_max_left _ _,le_max_right _ _⟩)
    (fun i => hCover i.1 i.2) P hz
  refine ⟨n,fun i => ?_⟩
  cases he : (p i).val with
  | none => exact True.intro
  | some q =>
    intro j hj
    exact hn (i,j) (Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr
        ⟨j,by simpa only [pins,he] using (List.mem_toFinset.mpr hj),rfl⟩⟩)

theorem symbolicRowProduct_natExpansion_relativeCCC
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (A : ℕ → I → J → Prop) (Z : I → J → Prop)
    (hB : BoundsCountableOmegaOneNames B)
    (hMono : ∀ n m,n ≤ m → ∀ i j,A n i j → A m i j)
    (hInto : ∀ n i j,A n i j → Z i j)
    (hCover : ∀ i j,Z i j → ∃ n,A n i j)
    (hCCC : ∀ n,ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (A n i)))) :
    ForcesRelativeCCC (rowProductQ (fun i => supportedSymbolicQ site (H i) (Z i))) := by
  let inc (n : ℕ) (p : ∀ i,SupportedSymbolic J (A n i)) (i : I) :
      SupportedSymbolic J (Z i) := includeNamedSupport (hInto n i) (p i)
  apply relativeCCC_of_countable_supported_union hB _
    (fun n => rowProductQ (fun i => supportedSymbolicQ site (H i) (A n i)))
    inc (fun _ _ => rfl) (fun _ _ _ => le_rfl) ?_ hCCC
  intro p
  obtain ⟨n,h⟩ := dependentFiniteRows_have_natStage A Z hMono hCover p
  refine ⟨n,fun i => ⟨(p i).val,h i⟩,?_⟩
  funext i
  exact Subtype.ext rfl

end JSP000930.Negative
