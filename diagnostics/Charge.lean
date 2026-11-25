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
