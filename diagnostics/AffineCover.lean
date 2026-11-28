import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_join
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

def par (a : V → Bool) (f : Finset V) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset V) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

def add (a b : V → Bool) (v : V) := xor (a v) (b v)

theorem par_add (a b : V → Bool) (f : Finset V) :
    par (add a b) f ↔ ¬(par a f ↔ par b f) := by
  unfold par
  have hf : f.filter (fun v => add a b v = true) =
      symmDiff (f.filter (fun v => a v = true)) (f.filter (fun v => b v = true)) := by
    ext x
    cases ha : a x <;> cases hb : b x <;>
      simp [Finset.mem_filter, Finset.mem_symmDiff, add, ha, hb]
  rw [hf]
  have := card_sd (f.filter (fun v => a v = true)) (f.filter (fun v => b v = true))
  simp only [Nat.odd_iff] at *
  omega

def twist (a b x : V → Bool) := add (add a b) x

theorem eq_twist (a b x : V → Bool) (q : LinEq V) :
    LinEqSat (twist a b x) q ↔ ((LinEqSat a q ↔ LinEqSat b q) ↔ LinEqSat x q) := by
  change (par (add (add a b) x) q.1 ↔ q.2 = true) ↔
    (((par a q.1 ↔ q.2 = true) ↔ (par b q.1 ↔ q.2 = true)) ↔ (par x q.1 ↔ q.2 = true))
  rw [par_add, par_add]
  tauto

theorem stable (a b x : V → Bool) (C : LinClause V)
    (ha : ¬LinClauseSat a C) (hb : ¬LinClauseSat b C) :
    LinClauseSat (twist a b x) C ↔ LinClauseSat x C := by
  have fixed : ∀ q ∈ C, LinEqSat (twist a b x) q ↔ LinEqSat x q := by
    intro q hq
    have av : ¬LinEqSat a q := fun h => ha ⟨q,hq,h⟩
    have bv : ¬LinEqSat b q := fun h => hb ⟨q,hq,h⟩
    rw [eq_twist]
    tauto
  exact ⟨fun ⟨q,m,t⟩ => ⟨q,m,(fixed q m).1 t⟩,
    fun ⟨q,m,t⟩ => ⟨q,m,(fixed q m).2 t⟩⟩

def Entails (C R : LinClause V) := ∀ x, LinClauseSat x C → LinClauseSat x R
def Together (C D R : LinClause V) := ∀ x, LinClauseSat x C → LinClauseSat x D → LinClauseSat x R
def opp (q : LinEq V) : LinEq V := (q.1,!q.2)

theorem opp_holds (q : LinEq V) (x : V → Bool) : LinEqSat x (opp q) ↔ ¬LinEqSat x q := by
  rcases q with ⟨f,b⟩
  cases b <;> simp [LinEqSat,opp]

theorem separator {C D R : LinClause V} (h : Together C D R)
    (nc : ¬Entails C R) (nd : ¬Entails D R) :
    ∃ q∈C, Entails C (insert q R) ∧ Entails D (insert (opp q) R) := by
  classical
  unfold Entails at nc nd
  push_neg at nc nd
  obtain ⟨a,ca,ra⟩ := nc
  obtain ⟨b,db,rb⟩ := nd
  obtain ⟨q,m,aq⟩ := ca
  have da : ¬LinClauseSat a D := fun s => ra (h a ⟨q,m,aq⟩ s)
  have cb : ¬LinClauseSat b C := fun s => rb (h b s db)
  have bq : ¬LinEqSat b q := fun s => cb ⟨q,m,s⟩
  have liftR (x : V → Bool) (p : LinEq V) (s : LinClauseSat x R) : LinClauseSat x (insert p R) := by
    obtain ⟨t,mt,v⟩ := s
    exact ⟨t,Finset.mem_insert_of_mem mt,v⟩
  refine ⟨q,m,?_,?_⟩
  · intro z cz
    by_cases rz : LinClauseSat z R
    · exact liftR z q rz
    by_cases zq : LinEqSat z q
    · exact ⟨q,Finset.mem_insert_self ..,zq⟩
    have dz : ¬LinClauseSat z D := fun s => rz (h z cz s)
    let w := twist a z b
    have dw : LinClauseSat w D := (stable a z b D da dz).2 db
    have rw' : ¬LinClauseSat w R := fun s => rb ((stable a z b R ra rz).1 s)
    have wq : LinEqSat w q := by
      change LinEqSat (twist a z b) q
      rw [eq_twist]
      tauto
    exact False.elim (rw' (h w ⟨q,m,wq⟩ dw))
  · intro z dz
    by_cases rz : LinClauseSat z R
    · exact liftR z (opp q) rz
    have zq : ¬LinEqSat z q := fun e => rz (h z ⟨q,m,e⟩ dz)
    exact ⟨opp q,Finset.mem_insert_self ..,(opp_holds q z).2 zq⟩
end PEqualNP.Outside.L_pcx_121_join
