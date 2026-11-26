import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4087.Rails

abbrev Pt := Fin 13
def D : Finset Pt := {0,1,3,9}
def core : Finset Pt := {0,2,3,7}
def ctr : Fin 9 → Pt := ![1,4,5,6,8,9,10,11,12]
def rotation : Fin 9 → Fin 3 := ![2,2,0,0,2,2,0,0,0]
def delta (j:Fin 9) : Pt := if rotation j=0 then 1 else if rotation j=1 then 3 else 9
def first (j:Fin 9) : Finset Pt := {ctr j,ctr j+delta j}
def second (j:Fin 9) : Finset Pt := {ctr j+3*delta j,ctr j+9*delta j}
def rail (i:Fin 18) : Finset Pt := if i.val % 2=0 then first (Fin.ofNat 9 (i.val/2)) else second (Fin.ofNat 9 (i.val/2))
def incident (p l:Pt) : Prop := p-l∈D
instance (p l:Pt) : Decidable (incident p l) := by unfold incident; infer_instance
def Arc (P:Finset Pt) : Prop := ∀l:Pt,(P.filter (fun p=>incident p l)).card≤2
def onRail (P:Finset Pt) (i:Fin 18) : Prop := ∃p∈rail i,p∈P
def hits (p:Pt) : Fin 3→Fin 18 := ![![2,13,16],![0,5,15],![1,7,17],![0,0,0],![1,2,8],![3,4,10],![4,6,13],![3,6,15],![5,8,17],![7,9,10],![0,11,12],![9,12,14],![11,14,16]] p
def mates (p:Pt) : Finset Pt := ![{4,6,12},{7,8,10},{4,8,9},∅,{0,2,8},{6,7,9},{0,5,7},{1,5,6},{1,2,4},{2,5,11},{1,11,12},{9,10,12},{0,10,11}] p
def carrier (p:Pt) : Pt := ![3,7,8,0,12,6,4,5,1,2,11,9,10] p

theorem rows : ∀ (p:Pt),p≠3 →
    (mates p).card = 3 := by decide +kernel
theorem line : ∀ (p:Pt),p≠3 → ∀q∈mates p,incident q (carrier p) := by decide +kernel
theorem direct : ∀ (p:Pt),p≠3 → ∀k:Fin 3,p∈rail (hits p k) := by decide +kernel
theorem partners : ∀ (p:Pt),p≠3 → ∀q∈mates p,∃k:Fin 3,∀ t∈rail (hits p k),t=p ∨ t=q := by decide +kernel

/-- The twelve noncentral raw point bits are reconstructed on every point arc by the
three pair signals selected in this nine-line configuration. -/
theorem recovered (P:Finset Pt) (ha:Arc P) (p:Pt) (hp:p≠3) :
    p∈P ↔ ∀k:Fin 3,onRail P (hits p k) := by
  constructor
  · exact fun h k=>⟨p,direct p hp k,h⟩
  · intro all
    by_contra hn
    have sub : mates p ⊆ P.filter (fun t=>incident t (carrier p)) := by
      intro q hq
      obtain ⟨k,hk⟩:=partners p hp q hq
      obtain ⟨u,hu,hm⟩:=all k
      rcases hk u hu with rfl|rfl
      · exact False.elim (hn hm)
      · exact Finset.mem_filter.mpr ⟨hm,line p hp _ hq⟩
    have count:=Finset.card_le_card sub
    rw [rows p hp] at count
    have small:=ha (carrier p)
    omega

theorem uncovered : ∀ l:Pt,l∈core ↔ ¬∃j:Fin 9,ctr j=l := by decide +kernel
theorem common : ∀ l∈core,incident 3 l := by decide +kernel
def source : Fin 41 → Nat := ![8193,8193,8193,8194,8194,8194,32772,32772,32772,65552,65552,65552,32800,32800,32800,65600,65600,65600,1048704,1048704,1048704,1048832,1048832,1048832,8704,8704,8704,1049600,1049600,1049600,34816,34816,34816,69632,69632,69632,8200,8193,32772,65544,1048584]
def counter : Fin 41 → Nat := ![61888,308368,4235728,4235728,2143424,177472,231170,4235728,1348113,623875,4270468,1378821,1102401,115585,61888,115585,1133089,92576,3182659,3211303,1079392,5253204,1247750,1609747,92576,8462756,208132,1194052,1247750,1217090,177472,185152,231170,346753,362113,208132,61888,115585,208132,416264,416264]
def diffMask : Fin 41 → Nat := ![536870913,35184372088833,1125899906842625,67108866,8589934594,281474976710658,134217732,68719476740,2251799813685252,134217744,536870928,274877906960,1073741856,4294967328,2199023255584,4294967360,34359738432,35184372088896,1073741952,34359738496,281474976710784,8589934848,274877907200,2251799813685504,68719477248,549755814400,2199023256064,67109888,4398046512128,17592186045440,549755815936,17592186046464,140737488357376,4398046515200,140737488359424,1125899906846720,8,8192,32768,65536,1048576]
def holes : Fin 66 → Nat := ![3,5,17,33,65,129,257,513,1025,2049,4097,6,18,34,66,130,258,514,1026,2050,4098,20,36,68,132,260,516,1028,2052,4100,48,80,144,272,528,1040,2064,4112,96,160,288,544,1056,2080,4128,192,320,576,1088,2112,4160,384,640,1152,2176,4224,768,1280,2304,4352,1536,2560,4608,3072,5120,6144]
def packed : Fin 66 → Fin 20 → Fin 41 := ![![36,37,38,39,40,3,0,4,1,5,6,18,13,16,24,11,30,33,29,23],![36,37,38,39,40,6,0,7,1,2,27,18,13,21,16,11,30,26,33,5],![36,37,38,39,40,9,0,11,1,2,27,18,13,4,16,7,25,33,31,23],![36,37,38,39,40,0,12,13,14,1,27,9,4,16,7,22,25,33,31,20],![36,37,38,39,40,0,15,16,1,2,27,9,18,4,7,22,25,14,33,31],![36,37,38,39,40,0,18,19,1,20,27,9,15,4,7,22,25,14,33,31],![36,37,38,39,40,0,21,22,1,2,27,9,18,13,16,7,30,26,33,5],![36,37,38,39,40,0,24,25,26,1,27,9,18,13,4,16,22,33,31,8],![36,37,38,39,40,27,0,28,29,1,6,18,13,21,16,24,11,30,34,5],![36,37,38,39,40,0,30,31,1,32,27,9,18,13,4,16,7,22,26,33],![36,37,38,39,40,0,33,1,34,2,3,6,18,13,21,16,24,11,30,29],![36,37,38,39,40,3,6,4,7,5,10,18,13,16,22,30,26,33,29,1],![36,37,38,39,40,3,9,10,4,11,18,13,16,7,30,26,33,29,1,23],![36,37,38,39,40,3,12,13,4,14,6,10,19,24,22,30,33,29,17,2],![36,37,38,39,40,3,15,4,16,17,6,10,18,24,22,30,14,33,29,2],![36,37,38,39,40,3,18,4,19,5,6,10,15,24,22,30,14,33,29,1],![36,37,38,39,40,3,4,22,5,23,6,10,18,13,16,24,30,33,29,1],![36,37,38,39,40,3,4,24,25,26,9,0,18,13,16,22,33,29,32,8],![36,37,38,39,40,3,4,28,29,5,6,10,18,13,16,24,22,30,1,34],![36,37,38,39,40,3,4,30,31,32,6,10,18,13,16,24,22,28,1,35],![36,37,38,39,40,3,4,33,34,5,6,10,18,13,16,24,22,30,29,1],![36,37,38,39,40,6,10,7,11,8,27,18,13,21,16,30,26,33,1,5],![36,37,38,39,40,6,12,13,7,14,27,10,4,16,22,25,33,31,1,20],![36,37,38,39,40,6,15,16,7,17,27,10,12,4,22,30,26,33,20,2],![36,37,38,39,40,6,18,19,7,20,27,10,15,4,22,25,14,33,31,1],![36,37,38,39,40,6,21,7,22,8,27,10,18,13,16,30,26,33,1,5],![36,37,38,39,40,6,7,25,26,8,27,10,18,13,4,16,22,33,31,1],![36,37,38,39,40,27,6,7,28,29,10,18,13,21,16,30,26,1,34,5],![36,37,38,39,40,6,7,30,31,32,27,10,18,13,4,16,22,26,33,1],![36,37,38,39,40,6,7,33,34,35,27,10,18,13,4,16,22,30,26,1],![36,37,38,39,40,9,10,12,13,11,27,4,19,7,25,33,31,17,2,23],![36,37,38,39,40,9,10,15,16,11,27,18,4,7,25,14,33,31,2,23],![36,37,38,39,40,9,10,18,19,11,27,15,4,7,25,14,33,31,1,23],![36,37,38,39,40,9,10,21,11,23,27,18,13,16,7,30,26,33,1,5],![36,37,38,39,40,9,10,24,11,25,27,18,13,21,16,33,31,1,5,8],![36,37,38,39,40,27,9,10,11,28,18,13,21,16,24,30,1,34,5,8],![36,37,38,39,40,9,10,11,30,31,27,18,13,4,16,7,26,33,1,23],![36,37,38,39,40,9,10,11,33,34,3,18,13,21,16,24,30,29,1,8],![36,37,38,39,40,12,13,16,14,17,27,6,10,4,24,22,30,33,20,2],![36,37,38,39,40,12,13,19,14,20,27,6,10,4,24,22,30,33,17,2],![36,37,38,39,40,12,13,21,22,14,27,9,0,19,7,25,33,31,17,5],![36,37,38,39,40,12,13,24,25,14,27,9,0,4,19,22,33,31,17,8],![36,37,38,39,40,27,12,13,14,28,6,10,4,16,24,22,30,1,34,20],![36,37,38,39,40,12,13,30,14,31,27,6,10,4,16,24,22,33,1,20],![36,37,38,39,40,12,13,14,33,34,27,6,10,4,16,24,22,30,1,20],![36,37,38,39,40,18,15,16,17,20,27,6,10,4,24,22,30,14,33,2],![36,37,38,39,40,15,21,16,22,17,27,6,10,18,24,30,14,33,5,2],![36,37,38,39,40,15,16,24,25,26,27,9,0,12,4,22,33,31,20,8],![36,37,38,39,40,27,15,16,28,29,6,10,18,21,24,30,14,34,5,2],![36,37,38,39,40,15,16,30,31,17,27,6,10,18,4,24,22,14,33,2],![36,37,38,39,40,15,16,33,17,34,3,6,0,18,21,24,11,30,14,29],![36,37,38,39,40,18,21,19,22,20,3,6,10,15,24,30,14,33,29,1],![36,37,38,39,40,18,19,24,25,26,27,9,0,13,4,22,33,31,17,8],![36,37,38,39,40,27,18,19,28,29,6,10,15,4,24,22,30,14,1,34],![36,37,38,39,40,18,19,30,31,32,27,6,10,15,4,24,22,14,33,1],![36,37,38,39,40,18,19,33,34,20,27,6,10,15,4,24,22,30,14,1],![36,37,38,39,40,21,24,22,25,26,27,6,10,18,13,16,33,31,1,5],![36,37,38,39,40,27,21,22,28,29,6,10,18,13,16,24,30,1,34,5],![36,37,38,39,40,21,22,30,31,32,27,6,10,18,13,16,24,33,1,5],![36,37,38,39,40,21,22,33,34,35,27,6,10,18,13,16,24,30,1,5],![36,37,38,39,40,27,24,25,26,28,9,0,18,13,21,16,32,5,35,8],![36,37,38,39,40,24,25,26,31,32,27,9,0,18,13,4,16,22,33,8],![36,37,38,39,40,24,25,26,33,34,27,9,0,18,13,4,16,22,31,8],![36,37,38,39,40,27,30,28,29,32,6,10,18,13,21,16,24,1,5,35],![36,37,38,39,40,27,28,29,34,35,6,10,18,13,21,16,24,30,1,5],![36,37,38,39,40,30,33,31,32,35,27,6,10,18,13,4,16,24,22,1]]

def pointSet (x:Nat) : Finset Pt := Finset.univ.filter (fun i:Pt=>x.testBit i.val=true)
def lineSet (x:Nat) : Finset Pt := Finset.univ.filter (fun i:Pt=>x.testBit (13+i.val)=true)
def pos (x:Nat) : Prop := ∃p l:Pt,pointSet x={p} ∧ lineSet x={l} ∧ l∈core ∧ incident p l
def neg (x:Nat) : Prop := (∀p∈pointSet x,∀l∈lineSet x,¬incident p l) ∧
  Arc (pointSet x) ∧ ∀p:Pt,((lineSet x).filter (fun l=>incident p l)).card≤2
instance (x:Nat) : Decidable (pos x) := by unfold pos; infer_instance
instance (x:Nat) : Decidable (neg x) := by unfold neg Arc; infer_instance
def store (v:Nat) (i:Fin 53) : Bool :=
  if i.val<26 then v.testBit i.val else
    let j:Fin 9:=Fin.ofNat 9 ((i.val-26)/3)
    let t:=(i.val-26)%3
    let a:=(first j).toList.any fun p=>v.testBit p.val
    let b:=(second j).toList.any fun p=>v.testBit p.val
    if t=0 then a else if t=1 then b else a || b

theorem data : ∀k:Fin 41,pos (source k) ∧ neg (counter k) := by decide +kernel
theorem differences : ∀(k:Fin 41) (i:Fin 53),store (source k) i=true →
  store (counter k) i=false → (diffMask k).testBit i.val=true := by decide +kernel
def allBits : Nat := 9007199254740991
theorem all_on : ∀i:Fin 53,allBits.testBit i.val=true := by decide +kernel
theorem packed_separates : ∀(r:Fin 66) (a b:Fin 20), a≠b →
   diffMask (packed r a) &&& diffMask (packed r b) &&& (allBits ^^^ holes r) = 0 := by decide +kernel
theorem index_holes : ∀p q:Pt,p≠3 → q≠3 → p≠q →
  ∃r:Fin 66,∀i:Fin 53,(holes r).testBit i.val=true ↔ i.val=p.val ∨ i.val=q.val := by decide +kernel

def Supports (U:Finset (Fin 53)) (F : (Fin 53→Bool)→Bool) : Prop :=
  ∀x y,(∀i∈U,x i=true → y i=true) → F x=true → F y=true

theorem needs_coordinate (F:(Fin 53→Bool)→Bool) (U:Finset (Fin 53)) (support:Supports U F)
    (yes:∀x,pos x→F (store x)=true) (no:∀x,neg x→F (store x)=false)
    (k:Fin 41) : ∃i∈U,(diffMask k).testBit i.val=true := by
  by_contra! h
  have hh:=support (store (source k)) (store (counter k)) (fun i hi hit=>by
    cases eq:store (counter k) i with
    | true => rfl
    | false => exact False.elim (by have a:=differences k i hit eq; simp_all)) (yes _ (data k).1)
  rw [no _ (data k).2] at hh
  contradiction

/-- Omitting two peripheral raw point coordinates in the symmetric pencil forces at least
20 distinct inputs to every correct monotone continuation. -/
theorem two_missing (F:(Fin 53→Bool)→Bool) (U:Finset (Fin 53)) (sup:Supports U F)
    (yes:∀x,pos x→F (store x)=true) (no:∀x,neg x→F (store x)=false)
    (p q:Pt) (hp:p≠3) (hq:q≠3) (hne:p≠q)
    (omit:∀i∈U,i.val≠p.val ∧ i.val≠q.val) : 20≤U.card := by
  classical
  obtain ⟨r,hr⟩:=index_holes p q hp hq hne
  have hn (a:Fin 20) := needs_coordinate F U sup yes no (packed r a)
  choose f fu hit using hn
  let into (a:Fin 20) : U := ⟨f a,fu a⟩
  have inj : Function.Injective into := by
    intro a b h
    by_contra ne
    have same:f a=f b:=congrArg Subtype.val h
    have bad:=congrArg (fun t:Nat=>t.testBit (f a).val) (packed_separates r a b ne)
    have forbid:(holes r).testBit (f a).val=false := by
      cases hbit:(holes r).testBit (f a).val with
      | false=>rfl
      | true=>
        rcases (hr _).mp hbit with ha|hb
        · exact False.elim ((omit _ (fu a)).1 ha)
        · exact False.elim ((omit _ (fu a)).2 hb)
    have hb:(diffMask (packed r b)).testBit (f a).val=true := same.symm ▸ hit b
    have ha:=hit a
    simp [Nat.testBit_and,Nat.testBit_xor,all_on,forbid,ha,hb] at bad
  simpa using Fintype.card_le_of_injective into inj
end PEqualNP.Outside.L_meta_4087.Rails
