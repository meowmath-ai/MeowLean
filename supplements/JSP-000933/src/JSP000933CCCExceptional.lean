import JSP000933CCCCluster

open Filter
open scoped Topology

namespace JSP000933
namespace OpenGraphForcing

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

def Independent (K : Set (X × X)) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, (x,y) ∉ K

theorem Independent.closure_r57 {K : Set (X × X)} (hK : IsOpen K)
    {S : Set X} (hS : Independent K S) : Independent K (closure S) := by
  intro x hx y hy hxy
  obtain ⟨U,V,hU,hxU,hV,hyV,hUV⟩ := mem_nhds_prod_iff'.mp (hK.mem_nhds hxy)
  obtain ⟨x',hx'U,hx'S⟩ := (mem_closure_iff.mp hx) U hU hxU
  obtain ⟨y',hy'V,hy'S⟩ := (mem_closure_iff.mp hy) V hV hyV
  exact hS x' hx'S y' hy'S (hUV ⟨hx'U,hy'V⟩)

def Exceptional (K : Set (X × X)) (G : Set (Sample X n)) : Set (Sample X n) :=
  {a | a ∈ G ∧ a.2 ∉ edgeCluster K G a.1}

theorem exceptional_countable_r57 [SecondCountableTopology X]
    (K : Set (X × X)) (G : Set (Sample X n))
    (hLower : ∀ H : Set (Sample X n), H ⊆ G → ¬ H.Countable →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ Matched K a.1 b.1) :
    (Exceptional K G).Countable := by
  classical
  let TU := ↥(TopologicalSpace.countableBasis (Fin n → X))
  let TV := ↥(TopologicalSpace.countableBasis X)
  let I := TU × TV
  let Bad (k : I) : Set (Sample X n) :=
    {a | a ∈ G ∧ a.1 ∈ k.1.1 ∧ a.2 ∈ k.2.1 ∧
      ∀ b ∈ G, b.1 ∈ k.1.1 → b.2 ∈ k.2.1 → ¬ Matched K a.1 b.1}
  have hBad (k : I) : (Bad k).Countable := by
    by_contra hC
    obtain ⟨a,ha,b,hb,_,hM⟩ := hLower (Bad k) (fun _ h => h.1) hC
    exact ha.2.2.2 b hb.1 hb.2.1 hb.2.2.1 hM
  have hI : (⋃ k, Bad k).Countable := Set.countable_iUnion hBad
  apply hI.mono
  intro a hEx
  have hN : ¬ (∀ U V, IsOpen U → a.1 ∈ U → IsOpen V → a.2 ∈ V →
      ∃ z ∈ G, z.1 ∈ U ∧ Matched K a.1 z.1 ∧ z.2 ∈ V) :=
    fun h => hEx.2 (mem_edgeCluster_iff_r56.mpr h)
  obtain ⟨U,hU⟩ := not_forall.mp hN
  obtain ⟨V,hV⟩ := not_forall.mp hU
  have hData : IsOpen U ∧ a.1 ∈ U ∧ IsOpen V ∧ a.2 ∈ V ∧
      ¬ (∃ z ∈ G, z.1 ∈ U ∧ Matched K a.1 z.1 ∧ z.2 ∈ V) := by
    simpa only [not_imp] using hV
  obtain ⟨U',hU',haU,hUU⟩ :=
    (TopologicalSpace.isBasis_countableBasis (Fin n → X)).exists_subset_of_mem_open hData.2.1 hData.1
  obtain ⟨V',hV',haV,hVV⟩ :=
    (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hData.2.2.2.1 hData.2.2.1
  refine Set.mem_iUnion.mpr ⟨(⟨U',hU'⟩,⟨V',hV'⟩),hEx.1,haU,haV,fun b hb hbU hbV hM => ?_⟩
  exact hData.2.2.2.2 ⟨b,hb,hUU hbU,hM,hVV hbV⟩

end OpenGraphForcing
end JSP000933
