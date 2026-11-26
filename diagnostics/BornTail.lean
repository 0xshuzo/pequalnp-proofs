import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18854.Factors
set_option maxHeartbeats 0
set_option maxRecDepth 32768
def terms : Fin 15→Nat := ![16897,9217,6145,16450,8322,4354,16420,2180,1284,8232,2120,776,4144,1104,656]
def part : Fin 15→Fin 6→Nat := ![![1,512,16384,513,16385,16896],![1,1024,8192,1025,8193,9216],![1,2048,4096,2049,4097,6144],![2,64,16384,66,16386,16448],![2,128,8192,130,8194,8320],![2,256,4096,258,4098,4352],![4,32,16384,36,16388,16416],![4,128,2048,132,2052,2176],![4,256,1024,260,1028,1280],![8,32,8192,40,8200,8224],![8,64,2048,72,2056,2112],![8,256,512,264,520,768],![16,32,4096,48,4112,4128],![16,64,1024,80,1040,1088],![16,128,512,144,528,640]]
def accept (x : Nat) : Bool := (List.finRange 15).any fun t => (x &&& terms t)==terms t
def meet (u v : Fin 15) := terms u &&& terms v ≠ 0
instance (u v : Fin 15) : Decidable (meet u v) := by unfold meet; infer_instance
def born (A B : Nat→Prop) (u : Fin 15) := (∃a,A (part u a)) ∧ ∃b,B (part u b)
def active (t i : Fin 15) := (terms t).testBit i.val
def Safe (A B : Nat→Prop) := ∀a b,A a→B b→accept (a ||| b)=true

private theorem incompatible : ∀(u v : Fin 15) (a b : Fin 6), ¬meet u v →
    accept (part u a ||| part v b)=false := by decide +kernel
private theorem cross : ∀u v : Fin 15,u≠v → meet u v →
    ∃ i : Fin 15,∀t : Fin 15, meet u t → meet v t → active t i=true := by decide +kernel
private theorem nonempty : ∀t : Fin 15,∃i,active t i=true := by decide +kernel
private theorem multiplicity : ∀i:Fin 15,(Finset.univ.filter (fun t:Fin 15=>active t i=true)).card=3 := by decide +kernel

theorem intersect {A B : Nat→Prop} (safe : Safe A B) {u v} (bu:born A B u) (bv:born A B v) : meet u v := by
  by_contra no
  obtain ⟨a,ha⟩:=bu.1
  obtain ⟨b,hb⟩:=bv.2
  have yes:=safe _ _ ha hb
  rw [incompatible _ _ _ _ no] at yes
  contradiction

/-- Every newly generated matching at a safe AND contains a common raw edge. -/
theorem common_edge {A B : Nat→Prop} (safe : Safe A B) :
    ∃i : Fin 15,∀t,born A B t → active t i=true := by
  classical
  by_cases two : ∃u v : Fin 15,born A B u ∧ born A B v ∧ u≠v
  · obtain ⟨u,v,hu,hv,ne⟩:=two
    obtain ⟨i,hi⟩:=cross _ _ ne (intersect safe hu hv)
    exact ⟨i,fun t ht=>hi t (intersect safe hu ht) (intersect safe hv ht)⟩
  by_cases any : ∃t:Fin 15,born A B t
  · obtain ⟨u,hu⟩:=any
    obtain ⟨i,hi⟩:=nonempty u
    refine ⟨i,fun t ht=>?_⟩
    have same:u=t := by by_contra ne; exact two ⟨u,t,hu,ht,ne⟩
    simpa [←same] using hi
  exact ⟨0,fun t ht=>False.elim (any ⟨t,ht⟩)⟩

theorem at_most_three {A B : Nat→Prop} (safe : Safe A B) (S : Finset (Fin 15))
    (all : ∀t∈S,born A B t) : S.card≤3 := by
  obtain ⟨i,hit⟩:=common_edge safe
  rw [←multiplicity i]
  apply Finset.card_le_card
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit t (all t ht)⟩

theorem root_factor {A B : Nat→Prop}
    (ma : ∀x y:Nat,x &&& y = x → A x → A y)
    (mb : ∀x y:Nat,x &&& y = x → B x → B y)
    (correct : ∀x:Nat,A x → B x → accept x=true) : Safe A B := by
  intro a b ha hb
  apply correct
  · exact ma a (a ||| b) (by apply Nat.eq_of_testBit_eq; intro j; cases x:a.testBit j <;> cases y:b.testBit j <;> simp [Nat.testBit_and,Nat.testBit_or,x,y]) ha
  · exact mb b (a ||| b) (by apply Nat.eq_of_testBit_eq; intro j; cases x:a.testBit j <;> cases y:b.testBit j <;> simp [Nat.testBit_and,Nat.testBit_or,x,y]) hb
end PEqualNP.Outside.L_meta_18854.Factors

namespace PEqualNP.Outside.L_meta_18854.Factors.Tail
def mask : Fin 20 → Nat := ![1,2,4,8,16,16896,9216,6144,16448,8320,4352,16416,2176,1280,8224,2112,768,4128,1088,640]
def on : Fin 20 → Nat := ![16897,16450,16420,8232,4144,16897,9217,6145,16450,8322,4354,16420,2180,1284,8232,2120,776,4144,1104,656]
def off : Fin 20 → Nat := ![16896,16448,16416,8224,4128,16385,8193,4097,16386,8194,4098,16388,2052,1028,8200,2056,520,4112,1040,528]

def project (x : Nat) (i : Fin 20) : Bool := (x &&& mask i)==mask i

private theorem switches : ∀i : Fin 20,
    accept (on i)=true ∧ accept (off i)=false ∧
    ∀j : Fin 20, j≠i → project (on i) j = project (off i) j := by decide +kernel

/-- The twenty signals of the standard pair-bank interface are all independently essential
on realizable primary assignments, including for signed continuation circuits. -/
theorem all_essential (T : (Fin 20 → Bool) → Bool)
    (correct : ∀x : Nat,T (project x)=accept x) (i : Fin 20) :
    ∃u v : Fin 20→Bool, (∀j,j≠i→u j=v j) ∧ T u=true ∧ T v=false := by
  obtain ⟨h,l,d⟩:=switches i
  exact ⟨project (on i),project (off i),d,(correct _).trans h,(correct _).trans l⟩

end PEqualNP.Outside.L_meta_18854.Factors.Tail
