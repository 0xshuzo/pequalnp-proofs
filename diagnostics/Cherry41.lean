import PEqualNP.Defs
open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_178.CherryPacking
abbrev V := Fin 5 × Fin 4
abbrev Word := List (Nat × Bool)
def wires : Array (Word × Nat) := #[([(0,true),(1,true),(2,true),(3,true)],0),([(4,true),(5,true),(6,true),(7,true)],0),([(8,true),(9,true),(10,true),(11,true)],0),([(12,true),(13,true),(14,true),(15,true)],0),([(16,true),(17,true),(18,true),(19,true)],0),([(0,false),(4,false)],1),([(1,false),(5,false)],2),([(2,false),(6,false)],3),([(3,false),(7,false)],4),([(0,false),(8,false)],5),([(1,false),(9,false)],6),([(2,false),(10,false)],7),([(3,false),(11,false)],8),([(0,false),(12,false)],9),([(1,false),(13,false)],10),([(2,false),(14,false)],11),([(3,false),(15,false)],12),([(0,false),(16,false)],13),([(1,false),(17,false)],14),([(2,false),(18,false)],15),([(3,false),(19,false)],16),([(4,false),(8,false)],17),([(5,false),(9,false)],18),([(6,false),(10,false)],19),([(7,false),(11,false)],20),([(4,false),(12,false)],21),([(5,false),(13,false)],22),([(6,false),(14,false)],23),([(7,false),(15,false)],24),([(4,false),(16,false)],25),([(5,false),(17,false)],26),([(6,false),(18,false)],27),([(7,false),(19,false)],28),([(8,false),(12,false)],29),([(9,false),(13,false)],30),([(10,false),(14,false)],31),([(11,false),(15,false)],32),([(8,false),(16,false)],33),([(9,false),(17,false)],34),([(10,false),(18,false)],35),([(11,false),(19,false)],36),([(12,false),(16,false)],37),([(13,false),(17,false)],38),([(14,false),(18,false)],39),([(15,false),(19,false)],40),([(1,true),(2,true),(3,true),(4,false)],1),([(0,true),(2,true),(3,true),(5,false)],2),([(0,true),(1,true),(3,true),(6,false)],3),([(0,true),(1,true),(2,true),(7,false)],4),([(1,true),(2,true),(3,true),(8,false)],5),([(0,true),(2,true),(3,true),(9,false)],6),([(0,true),(1,true),(3,true),(10,false)],7),([(0,true),(1,true),(2,true),(11,false)],8),([(1,true),(2,true),(3,true),(12,false)],9),([(0,true),(2,true),(3,true),(13,false)],10),([(0,true),(1,true),(3,true),(14,false)],11),([(0,true),(1,true),(2,true),(15,false)],12),([(1,true),(2,true),(3,true),(16,false)],13),([(0,true),(2,true),(3,true),(17,false)],14),([(0,true),(1,true),(3,true),(18,false)],15),([(0,true),(1,true),(2,true),(19,false)],16),([(5,true),(6,true),(7,true),(0,false)],1),([(4,true),(6,true),(7,true),(1,false)],2),([(4,true),(5,true),(7,true),(2,false)],3),([(4,true),(5,true),(6,true),(3,false)],4),([(5,true),(6,true),(7,true),(8,false)],17),([(4,true),(6,true),(7,true),(9,false)],18),([(4,true),(5,true),(7,true),(10,false)],19),([(4,true),(5,true),(6,true),(11,false)],20),([(5,true),(6,true),(7,true),(12,false)],21),([(4,true),(6,true),(7,true),(13,false)],22),([(4,true),(5,true),(7,true),(14,false)],23),([(4,true),(5,true),(6,true),(15,false)],24),([(5,true),(6,true),(7,true),(16,false)],25),([(4,true),(6,true),(7,true),(17,false)],26),([(4,true),(5,true),(7,true),(18,false)],27),([(4,true),(5,true),(6,true),(19,false)],28),([(9,true),(10,true),(11,true),(0,false)],5),([(8,true),(10,true),(11,true),(1,false)],6),([(8,true),(9,true),(11,true),(2,false)],7),([(8,true),(9,true),(10,true),(3,false)],8),([(9,true),(10,true),(11,true),(4,false)],17),([(8,true),(10,true),(11,true),(5,false)],18),([(8,true),(9,true),(11,true),(6,false)],19),([(8,true),(9,true),(10,true),(7,false)],20),([(9,true),(10,true),(11,true),(12,false)],29),([(8,true),(10,true),(11,true),(13,false)],30),([(8,true),(9,true),(11,true),(14,false)],31),([(8,true),(9,true),(10,true),(15,false)],32),([(9,true),(10,true),(11,true),(16,false)],33),([(8,true),(10,true),(11,true),(17,false)],34),([(8,true),(9,true),(11,true),(18,false)],35),([(8,true),(9,true),(10,true),(19,false)],36),([(13,true),(14,true),(15,true),(0,false)],9),([(12,true),(14,true),(15,true),(1,false)],10),([(12,true),(13,true),(15,true),(2,false)],11),([(12,true),(13,true),(14,true),(3,false)],12),([(13,true),(14,true),(15,true),(4,false)],21),([(12,true),(14,true),(15,true),(5,false)],22),([(12,true),(13,true),(15,true),(6,false)],23),([(12,true),(13,true),(14,true),(7,false)],24),([(13,true),(14,true),(15,true),(8,false)],29),([(12,true),(14,true),(15,true),(9,false)],30),([(12,true),(13,true),(15,true),(10,false)],31),([(12,true),(13,true),(14,true),(11,false)],32),([(13,true),(14,true),(15,true),(16,false)],37),([(12,true),(14,true),(15,true),(17,false)],38),([(12,true),(13,true),(15,true),(18,false)],39),([(12,true),(13,true),(14,true),(19,false)],40),([(17,true),(18,true),(19,true),(0,false)],13),([(16,true),(18,true),(19,true),(1,false)],14),([(16,true),(17,true),(19,true),(2,false)],15),([(16,true),(17,true),(18,true),(3,false)],16),([(17,true),(18,true),(19,true),(4,false)],25),([(16,true),(18,true),(19,true),(5,false)],26),([(16,true),(17,true),(19,true),(6,false)],27),([(16,true),(17,true),(18,true),(7,false)],28),([(17,true),(18,true),(19,true),(8,false)],33),([(16,true),(18,true),(19,true),(9,false)],34),([(16,true),(17,true),(19,true),(10,false)],35),([(16,true),(17,true),(18,true),(11,false)],36),([(17,true),(18,true),(19,true),(12,false)],37),([(16,true),(18,true),(19,true),(13,false)],38),([(16,true),(17,true),(19,true),(14,false)],39),([(16,true),(17,true),(18,true),(15,false)],40)]
def samples : Array Nat := #[0,541201,540962,532804,270728,540961,541202,533524,272408,529441,533522,541204,295448,99361,164882,295444,541208,540946,541217,533569,272513,529426,533537,541249,295553,99346,164897,295489,541313,528706,533057,541729,296993,98626,164417,295969,542753,71746,141377,280609,558113]
def cell (q : Nat) : V := (⟨q / 4 % 5,Nat.mod_lt _ (by decide)⟩,⟨q % 4,Nat.mod_lt _ (by decide)⟩)
def place (v : V) := 4*v.1.val+v.2.val
def point (i : Fin 41) (v : V) := (samples[i.val]!).testBit (place v)
def word (j : Fin 125) : Word := (wires[j.val]!).1
def tag (j : Fin 125) : Nat := (wires[j.val]!).2
def decode (ls : Word) : LinClause V :=
  linOfClause ((ls.map fun q => (cell q.1,q.2)).toFinset)
def check (j : Fin 125) (i : Fin 41) :=
  decide (i.val=tag j) || (word j).any (fun q => point i (cell q.1)==q.2)
theorem satCode (a : V → Bool) (ls : Word)
    (h : ls.any (fun q => a (cell q.1)==q.2) = true) : LinClauseSat a (decode ls) := by
  obtain ⟨q,hq,holds⟩:=List.any_eq_true.mp h
  have eq : a (cell q.1)=q.2 := beq_iff_eq.mp holds
  refine ⟨({cell q.1},q.2),Finset.mem_image.mpr ⟨(cell q.1,q.2),?_,rfl⟩,?_⟩
  · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,hq,rfl⟩)
  · cases b : q.2 <;> simp [LinEqSat,eq,b]

theorem slab0 : ∀ (x : Fin 10) (i : Fin 41), check ⟨0+x.val,by omega⟩ i = true := by decide +kernel
theorem slab1 : ∀ (x : Fin 10) (i : Fin 41), check ⟨10+x.val,by omega⟩ i = true := by decide +kernel
theorem slab2 : ∀ (x : Fin 10) (i : Fin 41), check ⟨20+x.val,by omega⟩ i = true := by decide +kernel
theorem slab3 : ∀ (x : Fin 10) (i : Fin 41), check ⟨30+x.val,by omega⟩ i = true := by decide +kernel
theorem slab4 : ∀ (x : Fin 10) (i : Fin 41), check ⟨40+x.val,by omega⟩ i = true := by decide +kernel
theorem slab5 : ∀ (x : Fin 10) (i : Fin 41), check ⟨50+x.val,by omega⟩ i = true := by decide +kernel
theorem slab6 : ∀ (x : Fin 10) (i : Fin 41), check ⟨60+x.val,by omega⟩ i = true := by decide +kernel
theorem slab7 : ∀ (x : Fin 10) (i : Fin 41), check ⟨70+x.val,by omega⟩ i = true := by decide +kernel
theorem slab8 : ∀ (x : Fin 10) (i : Fin 41), check ⟨80+x.val,by omega⟩ i = true := by decide +kernel
theorem slab9 : ∀ (x : Fin 10) (i : Fin 41), check ⟨90+x.val,by omega⟩ i = true := by decide +kernel
theorem slab10 : ∀ (x : Fin 10) (i : Fin 41), check ⟨100+x.val,by omega⟩ i = true := by decide +kernel
theorem slab11 : ∀ (x : Fin 10) (i : Fin 41), check ⟨110+x.val,by omega⟩ i = true := by decide +kernel
theorem slab12 : ∀ (x : Fin 5) (i : Fin 41), check ⟨120+x.val,by omega⟩ i = true := by decide +kernel

theorem audits (j : Fin 125) (i : Fin 41) : check j i=true := by
  by_cases t0 : j.val < 10
  · have h:=slab0 ⟨j.val-0,by omega⟩ i
    have e : (⟨0+(j.val-0),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t1 : j.val < 20
  · have h:=slab1 ⟨j.val-10,by omega⟩ i
    have e : (⟨10+(j.val-10),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t2 : j.val < 30
  · have h:=slab2 ⟨j.val-20,by omega⟩ i
    have e : (⟨20+(j.val-20),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t3 : j.val < 40
  · have h:=slab3 ⟨j.val-30,by omega⟩ i
    have e : (⟨30+(j.val-30),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t4 : j.val < 50
  · have h:=slab4 ⟨j.val-40,by omega⟩ i
    have e : (⟨40+(j.val-40),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t5 : j.val < 60
  · have h:=slab5 ⟨j.val-50,by omega⟩ i
    have e : (⟨50+(j.val-50),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t6 : j.val < 70
  · have h:=slab6 ⟨j.val-60,by omega⟩ i
    have e : (⟨60+(j.val-60),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t7 : j.val < 80
  · have h:=slab7 ⟨j.val-70,by omega⟩ i
    have e : (⟨70+(j.val-70),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t8 : j.val < 90
  · have h:=slab8 ⟨j.val-80,by omega⟩ i
    have e : (⟨80+(j.val-80),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t9 : j.val < 100
  · have h:=slab9 ⟨j.val-90,by omega⟩ i
    have e : (⟨90+(j.val-90),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t10 : j.val < 110
  · have h:=slab10 ⟨j.val-100,by omega⟩ i
    have e : (⟨100+(j.val-100),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t11 : j.val < 120
  · have h:=slab11 ⟨j.val-110,by omega⟩ i
    have e : (⟨110+(j.val-110),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
    exact e ▸ h
  have h:=slab12 ⟨j.val-120,by omega⟩ i
  have e : (⟨120+(j.val-120),by omega⟩ : Fin 125)=j := Fin.ext (by dsimp; omega)
  exact e ▸ h

def Sector (c : LinClause V) := ∃ j : Fin 125, ∀ a, LinClauseSat a (decode (word j)) → LinClauseSat a c

theorem oneLabel {c : LinClause V} (s : Sector c) {x y : Fin 41}
    (bad : ¬LinClauseSat (point x) c) (bad' : ¬LinClauseSat (point y) c) : x=y := by
  obtain ⟨j,w⟩:=s
  have marked (i : Fin 41) (fail : ¬LinClauseSat (point i) c) : i.val=tag j := by
    by_contra ne
    have ok:=audits j i
    have sat : (word j).any (fun q => point i (cell q.1)==q.2)=true := by
      simpa [check,ne] using ok
    exact fail (w _ (satCode _ _ sat))
  exact Fin.ext ((marked x bad).trans (marked y bad').symm)

theorem pricing (U : Finset (LinClause V)) (ok : ∀ c ∈ U,Sector c)
    (cover : ∀ a : V→Bool, ∃ c∈U, ¬LinClauseSat a c) : 41 ≤ U.card := by
  classical
  choose C inU bad using fun i : Fin 41 => cover (point i)
  let f (i : Fin 41) : U := ⟨C i,inU i⟩
  have inj : Function.Injective f := by
    intro a b eq
    have e : C a=C b := congrArg Subtype.val eq
    exact oneLabel (ok _ (inU a)) (bad a) (e.symm ▸ bad b)
  have h:=Fintype.card_le_of_injective f inj
  simpa using h

end PEqualNP.Outside.L_pcx_178.CherryPacking
