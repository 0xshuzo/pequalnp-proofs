import Mathlib
import PEqualNP.Outside.L_meta_3483
import PEqualNP.Outside.L_meta_1737
namespace Class4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3483_aux

def Cover {n : Nat} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :=
   ∀u v,G.Adj u v → u∈S ∨ v∈S
def C4 {n : Nat} (G : SimpleGraph (Fin n)) :=
   ∀u v a b, u≠v → a≠b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False

lemma minimum {n : Nat} (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), Cover G S ∧ ∀T,Cover G T → S.card ≤ T.card := by
  classical
  let fam := (Finset.univ : Finset (Finset (Fin n))).filter (Cover G)
  have all : (Finset.univ : Finset (Fin n))∈fam :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i _ _=>Or.inl (Finset.mem_univ i)⟩
  obtain ⟨S,hS,hmin⟩ := fam.exists_min_image Finset.card ⟨_,all⟩
  exact ⟨S,(Finset.mem_filter.mp hS).2,fun T hT=>hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩)⟩

theorem classLower {n : Nat} (G : SimpleGraph (Fin n)) (C : Circuit) (c4 : C4 G)
    (mono : Monotone2 C)
    (truth : ∀ x : Fin n→Bool,C.eval (List.ofFn x)=true ↔ ∃u v,G.Adj u v ∧ x u=true ∧ x v=true)
    (good : G.IsAcyclic ∨ ((∀u,∃a b,a≠b ∧ G.Adj u a ∧ G.Adj u b) ∧ G.edgeSet.ncard ≤ n)) :
    ∃ S : Finset (Fin n), Cover G S ∧ G.edgeSet.ncard + S.card ≤ C.size+1 := by
  classical
  obtain ⟨S,hs,min⟩ := minimum G
  by_cases non : ∃a b,G.Adj a b
  · refine ⟨S,hs,?_⟩
    rcases good with forest|⟨deg,sparse⟩
    · apply PEqualNP.Outside.L_meta_1737 n S.card G C non _ ⟨S,hs,rfl⟩ min mono truth forest
      intro a b c d _ ac _ _ bd _ ab bc cd da
      exact c4 a c b d ac bd ab da.symm bc.symm cd
    · have high (u : Fin n) : 2 ≤ (G.neighborSet u).ncard := by
        rw [SimpleGraph.ncard_neighborSet,SimpleGraph.degree]
        obtain ⟨a,b,d,ha,hb⟩ := deg u
        exact Finset.one_lt_card.mpr ⟨a,SimpleGraph.mem_neighborFinset.mpr ha,b,
          SimpleGraph.mem_neighborFinset.mpr hb,d⟩
      have twins (v w : Fin n) (d : v≠w) (_ : ¬G.Adj v w)
          (_ : 2≤(G.neighborSet v).ncard) (_ : 2≤(G.neighborSet w).ncard) :
          ∃u,¬(G.Adj v u ↔ G.Adj w u) := by
        obtain ⟨a,b,ne,A,B⟩ := deg v
        by_contra! eq
        exact c4 v w a b d ne A B ((eq a).mp A) ((eq b).mp B)
      have adj (u v : Fin n) (uv : G.Adj u v)
          (_ : 2≤(G.neighborSet u).ncard) (_ : 2≤(G.neighborSet v).ncard) :
          ∃a b,G.Adj u a ∧ a≠v ∧ G.Adj v b ∧ b≠u ∧ (a=b ∨ ¬G.Adj a b) := by
        have other (s t : Fin n) : ∃a,G.Adj s a ∧ a≠t := by
          obtain ⟨a,b,d,ha,hb⟩ := deg s
          by_cases h : a=t
          · exact ⟨b,hb,fun e=>d (h.trans e.symm)⟩
          · exact ⟨a,ha,h⟩
        obtain ⟨a,ua,av⟩ := other u v
        obtain ⟨b,vb,bu⟩ := other v u
        exact ⟨a,b,ua,av,vb,bu,Or.inr (fun ab=>c4 u b v a bu.symm av.symm uv ua vb.symm ab.symm)⟩
      have ev : GraphEval C G := by
        intro u v
        change C.eval (List.ofFn (point {u,v}))=true ↔ _
        rw [truth]
        constructor
        · rintro ⟨a,b,ab,ha,hb⟩
          simp [point] at ha hb
          rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
          · exact (G.irrefl _ ab).elim
          · exact ab
          · exact ab.symm
          · exact (G.irrefl _ ab).elim
        · intro uv
          exact ⟨u,v,uv,by simp [point],by simp [point]⟩
      have h := pair_bound n S.card G C (fun v=>
        let ⟨a,_,_,ha,_⟩ := deg v; ⟨a,ha⟩) twins adj
          (fun T hT=>min T (fun u v uv=>hT u v uv (high _) (high _))) mono ev
      omega
  · refine ⟨∅,fun a b ab=>(non ⟨a,b,ab⟩).elim,?_⟩
    have empty : G.edgeSet=∅ := by
      ext z; induction z using Sym2.ind with
      | _ a b => simp only [SimpleGraph.mem_edgeSet,Set.mem_empty_iff_false,iff_false]; exact fun ab=>non ⟨a,b,ab⟩
    simp [empty]
end Class4970

namespace Bip4970
open Class4970 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
def left (m : ℕ) {n : ℕ} (a : Fin n) : Fin (n + m) := Fin.castAdd m a
def right (n : ℕ) {m : ℕ} (b : Fin m) : Fin (n + m) := Fin.natAdd n b

lemma disjoint_lr {n m : ℕ} (a : Fin n) (b : Fin m) : left m a ≠ right n b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at h'
  have := a.isLt
  omega

def graph (n m : ℕ) (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n + m)) where
  Adj := fun u v => ∃ p ∈ E, u = left m p.1 ∧ v = right n p.2 ∨ v = left m p.1 ∧ u = right n p.2
  symm := ⟨by intro u v; rintro ⟨p, hp, h | h⟩; exact ⟨p, hp, Or.inr h⟩; exact ⟨p, hp, Or.inl h⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨p, hp, h | h⟩
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)⟩

def edge {n m : ℕ} (p : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(left m p.1, right n p.2)

lemma edge_injective {n m : ℕ} : Function.Injective (@edge n m) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with h | h
  · apply Prod.ext
    · apply Fin.ext
      simpa [left] using congrArg Fin.val h.1
    · apply Fin.ext
      have hh := congrArg Fin.val h.2
      simp [right] at hh
      omega
  · exact (disjoint_lr p.1 q.2 h.1).elim

lemma edges (n m : ℕ) (E : Finset (Fin n × Fin m)) :
    (graph n m E).edgeSet = ↑(E.image edge) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨p, hp, h | h⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2]⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2, Sym2.eq_swap]⟩
    · rintro ⟨p, hp, he⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact ⟨p, hp, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
      · exact ⟨p, hp, Or.inr ⟨h.1.symm, h.2.symm⟩⟩


abbrev L {p : Nat} (l : Nat) (a : Fin p) := Fin.castAdd l a
abbrev R {l : Nat} (p : Nat) (b : Fin l) := Fin.natAdd p b
lemma li {p l : Nat} : Function.Injective (@L p l) := by
  intro a b e; apply Fin.ext; exact congrArg (fun u : Fin (p+l)=>u.val) e
lemma ri {p l : Nat} : Function.Injective (@R l p) := by
  intro a b e
  have h := congrArg Fin.val e
  simp only [R,Fin.val_natAdd] at h
  exact Fin.ext (by omega)
lemma lr {p l : Nat} (a : Fin p) (b : Fin l) : L l a ≠ R p b := by
  intro e
  have h := congrArg Fin.val e
  simp only [L,R,Fin.val_castAdd,Fin.val_natAdd] at h
  have := a.isLt
  omega

def Nb {p l : Nat} (E : Finset (Fin p × Fin l)) : (Fin p ⊕ Fin l) → Fin (p+l) → Prop
  | .inl a,z => ∃b,(a,b)∈E ∧ z=R p b
  | .inr b,z => ∃a,(a,b)∈E ∧ z=L l a

theorem c4_Nb {p l : Nat} {E : Finset (Fin p × Fin l)}
    (C4 : ∀a a' b b', a≠a' → b≠b' → ¬((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E)) :
    ∀ c d u v, u≠v → Nb E c u → Nb E c v → Nb E d u → Nb E d v → c=d := by
  intro c d u v uv c₁ c₂ d₁ d₂
  rcases c with a|b <;> rcases d with f|g
  · obtain ⟨b,hb,rfl⟩ := c₁
    obtain ⟨b',hb',rfl⟩ := c₂
    obtain ⟨t,ht,et⟩ := d₁
    obtain ⟨s,hs,es⟩ := d₂
    obtain rfl := ri et
    obtain rfl := ri es
    by_contra ne
    exact C4 a f b b' (fun z=>ne (z ▸ rfl)) (fun z=>uv (z ▸ rfl)) ⟨hb,hb',ht,hs⟩
  · obtain ⟨b,_,e⟩ := c₁
    obtain ⟨a,_,f⟩ := d₁
    exact (lr a b (f.symm.trans e)).elim
  · obtain ⟨a,_,e⟩ := c₁
    obtain ⟨b,_,f⟩ := d₁
    exact (lr a b (e.symm.trans f)).elim
  · obtain ⟨a,ha,rfl⟩ := c₁
    obtain ⟨a',ha',rfl⟩ := c₂
    obtain ⟨t,ht,et⟩ := d₁
    obtain ⟨s,hs,es⟩ := d₂
    obtain rfl := li et
    obtain rfl := li es
    by_contra ne
    exact C4 a a' b g (fun z=>uv (z ▸ rfl)) (fun z=>ne (z ▸ rfl)) ⟨ha,ht,ha',hs⟩

def side {p l : Nat} : Fin (p+l) → Fin p ⊕ Fin l := Fin.addCases Sum.inl Sum.inr
def coord {p l : Nat} : Fin p ⊕ Fin l → Fin (p+l) := Sum.elim (L l) (R p)
lemma side_lt {p l : Nat} (a : Fin p) : side (L l a)=Sum.inl a := by simp [side,L]
lemma side_rt {p l : Nat} (b : Fin l) : side (R p b)=Sum.inr b := by simp [side,R]
lemma coord_side {p l : Nat} (u : Fin (p+l)) : coord (side u)=u := by
  refine Fin.addCases (fun a=>?_) (fun b=>?_) u
  · exact congrArg coord (side_lt a)
  · exact congrArg coord (side_rt b)
lemma neighbor {p l : Nat} (E : Finset (Fin p × Fin l)) (u v : Fin (p+l)) :
    (graph p l E).Adj u v ↔ Nb E (side u) v := by
  constructor
  · rintro ⟨⟨a,b⟩,he,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · rw [show side (left l a)=Sum.inl a from side_lt a]
      exact ⟨b,he,rfl⟩
    · rw [show side (right p b)=Sum.inr b from side_rt b]
      exact ⟨a,he,rfl⟩
  · intro h
    have eu := coord_side u
    cases e : side u with
    | inl a =>
      rw [e] at h eu
      obtain ⟨b,he,rfl⟩ := h
      exact ⟨(a,b),he,Or.inl ⟨eu.symm,rfl⟩⟩
    | inr b =>
      rw [e] at h eu
      obtain ⟨a,he,rfl⟩ := h
      exact ⟨(a,b),he,Or.inr ⟨rfl,eu.symm⟩⟩

theorem classes {p l : Nat} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (no4 : ∀a a' b b',a≠a' → b≠b' → ¬((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (hc : IsAO2 (p+l) C) (correct : ∀x : Fin (p+l)→Bool,circuitFun (p+l) C x=
      decide (∃a b,(a,b)∈E ∧ x (L l a)=true ∧ x (R p b)=true))
    (good : (graph p l E).IsAcyclic ∨
      ((∀u,∃a b,a≠b ∧ (graph p l E).Adj u a ∧ (graph p l E).Adj u b) ∧ E.card≤p+l)) :
    ∃S : Finset (Fin (p+l)), (∀a b,(a,b)∈E → L l a∈S ∨ R p b∈S) ∧ E.card + S.card ≤ C.size+1 := by
  classical
  let G := graph p l E
  have m : G.edgeSet.ncard=E.card := by
    rw [show G.edgeSet=↑(E.image edge) from edges p l E,Set.ncard_coe_finset,Finset.card_image_of_injective _ edge_injective]
  have forbid : C4 G := by
    intro u v a b uv ab u₁ u₂ v₁ v₂
    have eq := c4_Nb no4 (side u) (side v) a b ab ((neighbor E u a).mp u₁)
      ((neighbor E u b).mp u₂) ((neighbor E v a).mp v₁) ((neighbor E v b).mp v₂)
    exact uv ((coord_side u).symm.trans ((congrArg coord eq).trans (coord_side v)))
  have ev (x : Fin (p+l) → Bool) : C.eval (List.ofFn x)=true ↔ ∃u v,G.Adj u v ∧ x u=true ∧ x v=true := by
    change circuitFun (p+l) C x=true ↔ _
    rw [correct,decide_eq_true_eq]
    constructor
    · rintro ⟨a,b,he,ha,hb⟩
      exact ⟨L l a,R p b,⟨(a,b),he,Or.inl ⟨rfl,rfl⟩⟩,ha,hb⟩
    · rintro ⟨u,v,⟨⟨a,b⟩,he,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩,hu,hv⟩
      · exact ⟨a,b,he,hu,hv⟩
      · exact ⟨a,b,he,hv,hu⟩
  obtain ⟨S,cov,budget⟩ := classLower G C forbid (fun g hg=>⟨hc.1 g hg,(hc.2.2 g hg).le⟩) ev
    (by simpa only [m] using good)
  exact ⟨S,fun a b he=>cov (L l a) (R p b) ⟨(a,b),he,Or.inl ⟨rfl,rfl⟩⟩,m ▸ budget⟩
end Bip4970
