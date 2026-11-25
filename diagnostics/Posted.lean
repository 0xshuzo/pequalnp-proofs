import Mathlib
import PEqualNP.Outside.L_meta_3483
namespace StarCharge4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux

def one {n : Nat} (v : Fin n) (u : Fin n) := decide (u=v)
def outside {n : Nat} (Q : Finset (Fin n)) (u : Fin n) := decide (u∉Q)
def single {n : Nat} (C : Circuit) (w : Nat) (i : Fin n) := val C (one i) w=true

def multi {n : Nat} (C : Circuit) (w : Nat) (v : Fin n) := single C w v ∧ ∃z,z≠v ∧ single C w z
def Port {n : Nat} (C : Circuit) (r : Nat) (i : Fin 2) (v : Fin n) :=
  ∀z : Fin n,single C (opnd C r i) z ↔ z=v

theorem mono_of (n : Nat) (C : Circuit) (h : IsAO2 n C) : Monotone2 C :=
  fun g hg => ⟨h.1 g hg,(h.2.2 g hg).le⟩

theorem firstPort {n : Nat} {C : Circuit} (hc : IsAO2 n C) (Q : Finset (Fin n)) (v : Fin n)
    (witness : ∃w, val C (outside Q) w=false ∧ multi C w v) :
    ∃ (r : Fin C.gates.length) (i : Fin 2), (gateAt C r.val).op=GateOp.or ∧
      multi C (n+r.val) v ∧ (∀z,single C (n+r.val) z → z∈Q) ∧ Port C r.val i v := by
  classical
  let w := Nat.find witness
  have hw : val C (outside Q) w=false ∧ multi C w v := Nat.find_spec witness
  have prev (k : Nat) (hk : k<w) : ¬(val C (outside Q) k=false ∧ multi C k v) := Nat.find_min witness hk
  obtain ⟨hfalse,hv,z,hz,hzv⟩ := hw
  have hin : n≤w := by
    by_contra! hsmall
    let b : Fin n := ⟨w,hsmall⟩
    have v₀ : b=v := by simpa only [single,←show b.val=w from rfl,val_input,one,decide_eq_true_eq] using hv
    have z₀ : b=z := by simpa only [single,←show b.val=w from rfl,val_input,one,decide_eq_true_eq] using hzv
    exact hz (z₀.symm.trans v₀)
  have hout : w < n+C.gates.length := by
    by_contra! ho
    have e := val_beyond C (one v) ho
    exact Bool.false_ne_true (e ▸ hv)
  let j := w-n
  have eqw : n+j=w := by dsimp [j]; omega
  have hj : j<C.gates.length := by omega
  let g := gateAt C j
  have ge : g=C.gates[j] := List.getD_eq_getElem _ _ hj
  have get : C.gates[j]?=some g := by simp [ge,hj]
  have gm : g∈C.gates := by rw [ge]; exact List.getElem_mem ..
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (hc.2.2 g gm)
  have ea : a<w := by rw [←eqw]; exact hc.2.1 j hj a (by change a∈g.inputs; rw [ins]; simp)
  have eb : b<w := by rw [←eqw]; exact hc.2.1 j hj b (by change b∈g.inputs; rw [ins]; simp)
  have eval (x : Fin n → Bool) : val C x w = g.op.eval [val C x a,val C x b] := by
    rw [←eqw,val_gate C x get,ins]
    simp [operand,eqw,ea,eb]
  have allQ (u : Fin n) (hu : single C w u) : u∈Q := by
    by_contra no
    have le (i : Fin n) (h : one u i=true) : outside Q i=true := by
      obtain rfl : i=u := of_decide_eq_true h
      exact decide_eq_true no
    have h := acts_mono (mono_of n C hc) le w hu
    rw [hfalse] at h
    contradiction
  have posAnd (hop : g.op=GateOp.and) (u : Fin n) (hu : single C w u) :
      single C a u ∧ single C b u := by
    change val C (one u) w=true at hu
    rw [eval,hop] at hu
    simpa [single,GateOp.eval] using hu
  rcases hc.1 g gm with op|op
  · have A := posAnd op v hv
    have Z := posAnd op z hzv
    have noA := prev a ea
    have noB := prev b eb
    rw [eval,op] at hfalse
    have hf : val C (outside Q) a=false ∨ val C (outside Q) b=false := by
      cases q : val C (outside Q) a
      · exact Or.inl rfl
      · right; simpa [GateOp.eval,q] using hfalse
    rcases hf with h|h
    · exact (noA ⟨h,A.1,z,hz,Z.1⟩).elim
    · exact (noB ⟨h,A.2,z,hz,Z.2⟩).elim
  · have hf : val C (outside Q) a=false ∧ val C (outside Q) b=false := by
      rw [eval,op] at hfalse
      simpa [GateOp.eval] using hfalse
    have choices : single C a v ∨ single C b v := by
      change val C (one v) w=true at hv
      rw [eval,op] at hv
      simpa [single,GateOp.eval] using hv
    have uniq (t : Nat) (ht : t<w) (ff : val C (outside Q) t=false) (yes : single C t v) :
        ∀u : Fin n,single C t u ↔ u=v := by
      intro u
      constructor
      · intro hu; by_contra ne; exact prev t ht ⟨ff,yes,u,ne,hu⟩
      · rintro rfl; exact yes
    have tail (i : Fin 2) (P : Port C j i v) : ∃ (r : Fin C.gates.length) (i : Fin 2),
        (gateAt C r.val).op=GateOp.or ∧ multi C (n+r.val) v ∧
        (∀z,single C (n+r.val) z → z∈Q) ∧ Port C r.val i v := by
      exact ⟨⟨j,hj⟩,i,op,by simpa only [eqw] using (show multi C w v from ⟨hv,z,hz,hzv⟩),by simpa only [eqw] using allQ,P⟩
    rcases choices with ha|hb
    · apply tail 0
      have e : opnd C j 0=a := by change (g.inputs.getD 0 0)=a; simp [ins]
      simpa only [Port,e] using uniq a ea hf.1 ha
    · apply tail 1
      have e : opnd C j 1=b := by change (g.inputs.getD 1 0)=b; simp [ins]
      simpa only [Port,e] using uniq b eb hf.2 hb
end StarCharge4970
namespace StarCharge4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
theorem ledger {n : Nat} {C : Circuit} (hc : IsAO2 n C)
    {A X : Type} [Fintype A] [DecidableEq X] [DecidableEq A]
    (centre : A → X) (leaf : A → Fin n) (neigh : X → Fin n → Prop)
    (inj : ∀e f, centre e=centre f → leaf e=leaf f → e=f)
    (c4 : ∀ c d u v, u≠v → neigh c u → neigh c v → neigh d u → neigh d v → c=d)
    (star : ∀e, ∃Q : Finset (Fin n), (∀z∈Q,neigh (centre e) z) ∧
       ∃w, val C (outside Q) w=false ∧ multi C w (leaf e)) :
    Fintype.card A ≤ 2*(Finset.univ.filter (fun r : Fin C.gates.length =>
      (gateAt C r.val).op=GateOp.or)).card := by
  classical
  let OS := Finset.univ.filter (fun r : Fin C.gates.length => (gateAt C r.val).op=GateOp.or)
  have found (e : A) : ∃ r : OS, ∃i : Fin 2, Port C r.val.val i (leaf e) ∧
      multi C (n+r.val.val) (leaf e) ∧ (∀z,single C (n+r.val.val) z → neigh (centre e) z) := by
    obtain ⟨Q,sub,w⟩ := star e
    obtain ⟨r,i,op,m,s,pt⟩ := firstPort hc Q (leaf e) w
    exact ⟨⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,op⟩⟩,i,pt,m,fun z h=>sub z (s z h)⟩
  choose row port hport hm hn using found
  let f (e : A) := (row e,port e)
  have hi : Function.Injective f := by
    intro e d eq
    have r : row e=row d := congrArg Prod.fst eq
    have s : port e=port d := congrArg Prod.snd eq
    have nr (z : Fin n) (hz : single C (n+(row e).val.val) z) := hn d z (r ▸ hz)
    obtain ⟨h₁,z,hz,h₂⟩ := hm e
    have same : centre e=centre d :=
      c4 _ _ _ _ hz (hn e z h₂) (hn e _ h₁) (nr z h₂) (nr _ h₁)
    apply inj _ _ same
    have m := (hport e (leaf e)).2 rfl
    rw [r,s] at m
    exact (hport d (leaf e)).1 m
  have q := Fintype.card_le_of_injective f hi
  change Fintype.card A ≤ 2*OS.card
  simpa only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.mul_comm OS.card 2] using q
end StarCharge4970
namespace StarCharge4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

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

theorem liftStar {n : Nat} {C : Circuit} {B : Type} [DecidableEq B] (f : B → Fin n)
    (hf : Function.Injective f) (Q : Finset B) (b : B) (hb : b∈Q) (hq : 2≤Q.card) (w : Nat)
    (he : ∀x:Fin n→Bool,val C x w=decide (∃t∈Q,x (f t)=true)) :
    val C (outside (Q.image f)) w=false ∧ multi C w (f b) := by
  have pos (t : B) (ht : t∈Q) : single C w (f t) := by
    rw [single,he]
    exact decide_eq_true ⟨t,ht,by simp [one]⟩
  constructor
  · rw [he]
    apply decide_eq_false
    rintro ⟨t,ht,p⟩
    have h : f t ∈ Q.image f := Finset.mem_image_of_mem f ht
    simp [outside,h] at p
  · refine ⟨pos b hb,?_⟩
    obtain ⟨t,ht,u,hu,d⟩ := Finset.one_lt_card.mp (by omega : 1<Q.card)
    by_cases e : t=b
    · exact ⟨f u,fun eq=>d (e.trans (hf eq).symm),pos u hu⟩
    · exact ⟨f t,fun eq=>e (hf eq),pos t ht⟩

def via {p l : Nat} (C : Circuit) {B : Type} [DecidableEq B] (f : B → Fin (p+l))
    (neigh : B → Prop) (v : B) := ∃j : Nat, ∃Q : Finset B, j<C.gates.length ∧
    (gateAt C j).op=GateOp.or ∧ 2≤Q.card ∧ v∈Q ∧ (∀z∈Q,neigh z) ∧
      ∀x : Fin (p+l) → Bool, val C x (p+l+j)=decide (∃z∈Q,x (f z)=true)

theorem posted_half {p l : Nat} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (C4 : ∀a a' b b', a≠a' → b≠b' → ¬((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (hc : IsAO2 (p+l) C)
    (served : ∀a b,(a,b)∈E → via (p:=p) (l:=l) C (R p) (fun t=>(a,t)∈E) b ∨
        via (p:=p) (l:=l) C (L l) (fun t=>(t,b)∈E) a) :
    E.card ≤ 2*(Finset.univ.filter (fun r : Fin C.gates.length =>
      (gateAt C r.val).op=GateOp.or)).card := by
  classical
  have pick (e : E) : ∃ (c : Fin p ⊕ Fin l) (v : Fin (p+l)),
      ((c=Sum.inl e.val.1 ∧ v=R p e.val.2) ∨ (c=Sum.inr e.val.2 ∧ v=L l e.val.1)) ∧
      ∃Q : Finset (Fin (p+l)), (∀z∈Q,Nb E c z) ∧ ∃w,val C (outside Q) w=false ∧ multi C w v := by
    rcases served _ _ e.property with ⟨j,S,_,_,hs,mem,ok,he⟩|⟨j,S,_,_,hs,mem,ok,he⟩
    · refine ⟨Sum.inl e.val.1,R p e.val.2,Or.inl ⟨rfl,rfl⟩,S.image (R p),?_,p+l+j,
        liftStar _ ri S _ mem hs _ he⟩
      intro z h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      exact ⟨t,ok t ht,rfl⟩
    · refine ⟨Sum.inr e.val.2,L l e.val.1,Or.inr ⟨rfl,rfl⟩,S.image (L l),?_,p+l+j,
        liftStar _ li S _ mem hs _ he⟩
      intro z h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      exact ⟨t,ok t ht,rfl⟩
  choose c v dir good using pick
  have inj (e f : E) (ce : c e=c f) (ve : v e=v f) : e=f := by
    rcases dir e with ⟨a,b⟩|⟨a,b⟩ <;> rcases dir f with ⟨d,h⟩|⟨d,h⟩ <;>
      rw [a,d] at ce <;> rw [b,h] at ve
    · exact Subtype.ext (Prod.ext (Sum.inl.inj ce) (ri ve))
    · contradiction
    · contradiction
    · exact Subtype.ext (Prod.ext (li ve) (Sum.inr.inj ce))
  simpa using ledger hc c v (Nb E) inj (c4_Nb C4) good
end StarCharge4970
