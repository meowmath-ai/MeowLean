import Mathlib

open Filter
open scoped Topology

namespace JSP000933
namespace OpenGraphForcing

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

abbrev Sample (X : Type*) (n : ℕ) := (Fin n → X) × X

def Matched (K : Set (X × X)) (p q : Fin n → X) : Prop :=
  ∀ i, (p i,q i) ∈ K

theorem isOpen_matched_r56 {K : Set (X × X)} (hK : IsOpen K) (p : Fin n → X) :
    IsOpen {q | Matched K p q} := by
  have he : {q | Matched K p q} =
      ⋂ i : Fin n, (fun q : Fin n → X => (p i,q i)) ⁻¹' K := by
    ext q
    simp [Matched]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => hK.preimage (continuous_const.prodMk (continuous_apply i)))

def imageAround (K : Set (X × X)) (G : Set (Sample X n)) (p : Fin n → X)
    (U : Set (Fin n → X)) : Set X :=
  {z | ∃ q, (q,z) ∈ G ∧ q ∈ U ∧ Matched K p q}

def edgeCluster (K : Set (X × X)) (G : Set (Sample X n)) (p : Fin n → X) : Set X :=
  ⋂ U : {U : Set (Fin n → X) // IsOpen U ∧ p ∈ U}, closure (imageAround K G p U.1)

theorem isClosed_edgeCluster_r56 (K : Set (X × X)) (G : Set (Sample X n)) (p : Fin n → X) :
    IsClosed (edgeCluster K G p) :=
  isClosed_iInter (fun _ => isClosed_closure)

theorem mem_edgeCluster_iff_r56 {K : Set (X × X)} {G : Set (Sample X n)}
    {p : Fin n → X} {z : X} :
    z ∈ edgeCluster K G p ↔
      ∀ U V, IsOpen U → p ∈ U → IsOpen V → z ∈ V →
        ∃ a ∈ G, a.1 ∈ U ∧ Matched K p a.1 ∧ a.2 ∈ V := by
  constructor
  · intro h U V hU hp hV hz
    have hh := Set.mem_iInter.mp h (⟨U,hU,hp⟩ : {U : Set (Fin n → X) // IsOpen U ∧ p ∈ U})
    obtain ⟨y,hyV,hyG⟩ := (mem_closure_iff.mp hh) V hV hz
    obtain ⟨q,hq,hqU,hqK⟩ := hyG
    exact ⟨(q,y),hq,hqU,hqK,hyV⟩
  · intro h
    apply Set.mem_iInter.mpr
    intro U
    apply mem_closure_iff.mpr
    intro V hV hz
    obtain ⟨a,ha,haU,haK,haV⟩ := h U.1 V U.2.1 U.2.2 hV hz
    exact ⟨a.2,haV,⟨a.1,ha,haU,haK⟩⟩

theorem edgeCluster_eq_of_dense_subgraph_r56 {K : Set (X × X)} (hK : IsOpen K)
    {G D : Set (Sample X n)} (hD : D ⊆ G) (hDense : G ⊆ closure D) (p : Fin n → X) :
    edgeCluster K G p = edgeCluster K D p := by
  ext z
  simp only [mem_edgeCluster_iff_r56]
  constructor
  · intro h U V hU hp hV hz
    obtain ⟨a,ha,haU,haK,haV⟩ := h U V hU hp hV hz
    let W := (U ∩ {q | Matched K p q}) ×ˢ V
    have hW : IsOpen W := (hU.inter (isOpen_matched_r56 hK p)).prod hV
    obtain ⟨b,hb,hbD⟩ := (mem_closure_iff.mp (hDense ha)) W hW ⟨⟨haU,haK⟩,haV⟩
    exact ⟨b,hbD,hb.1.1,hb.1.2,hb.2⟩
  · intro h U V hU hp hV hz
    obtain ⟨a,ha,haU,haK,haV⟩ := h U V hU hp hV hz
    exact ⟨a,hD ha,haU,haK,haV⟩

theorem exists_matched_samples_of_edgeCluster_r56 {K : Set (X × X)} (hK : IsOpen K)
    (hsym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K) {G : Set (Sample X n)}
    {p : Fin n → X} {x y : X} (hx : x ∈ edgeCluster K G p) (hy : y ∈ edgeCluster K G p)
    (hxy : (x,y) ∈ K) :
    ∃ a ∈ G, ∃ b ∈ G, Matched K a.1 b.1 ∧ (a.2,b.2) ∈ K := by
  obtain ⟨V,W,hV,hxV,hW,hyW,hProd⟩ := mem_nhds_prod_iff'.mp (hK.mem_nhds hxy)
  obtain ⟨a,ha,_,haK,haV⟩ := (mem_edgeCluster_iff_r56.mp hx) Set.univ V isOpen_univ
    (Set.mem_univ _) hV hxV
  let U := {q | Matched K a.1 q}
  have hU : IsOpen U := isOpen_matched_r56 hK a.1
  have hpU : p ∈ U := fun i => hsym (p i) (a.1 i) (haK i)
  obtain ⟨b,hb,hbU,_,hbW⟩ := (mem_edgeCluster_iff_r56.mp hy) U W hU hpU hW hyW
  exact ⟨a,ha,b,hb,hbU,hProd ⟨haV,hbW⟩⟩

end OpenGraphForcing
end JSP000933
