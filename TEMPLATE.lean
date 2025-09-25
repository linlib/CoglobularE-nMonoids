
def n : Int := 1


def reflexivity {X : Type} {x : X} (p : x = x) := Eq.refl p


def symmetry {X : Type} {x : X} {y : X}  (p : x = y) := Eq.symm p


def transitivity {X : Type} {x : X} {y : X} {z : X} (p : x = y) (q : y = z) := Eq.trans p q


def extensionality (f g : X → Y) (p : (x:X) → f x = g x) : f = g := funext p


def equal_arguments {X : Type} {Y : Type} {a : X} {b : X} (f : X → Y) (p : a = b) : f a = f b := congrArg f p

def equal_functions {X : Type} {Y : Type} {f₁ : X → Y} {f₂ : X → Y} (p : f₁ = f₂) (x : X) : f₁ x = f₂ x := congrFun p x

def pairwise {A : Type} {B : Type} (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) (p : a₁ = a₂) (q : b₁ = b₂) : (a₁,b₁)=(a₂,b₂) := (congr ((congrArg Prod.mk) p) q)


-- A category C consists of:
structure category.{u₀,v₀} where
  Obj : Type u₀
  Hom : Obj → Obj → Type v₀
  Idn : (X:Obj) → Hom X X
  Cmp : (X:Obj) → (Y:Obj) → (Z:Obj) → (_:Hom X Y) → (_:Hom Y Z) → Hom X Z
  Id₁ : (X:Obj) → (Y:Obj) → (f:Hom X Y) →
    Cmp X Y Y f (Idn Y) = f
  Id₂ : (X:Obj) → (Y:Obj) → (f:Hom X Y) →
    Cmp X X Y (Idn X) f = f
  Ass : (W:Obj) → (X:Obj) → (Y:Obj) → (Z:Obj) → (f:Hom W X) → (g:Hom X Y) → (h:Hom Y Z) →
    (Cmp W X Z) f (Cmp X Y Z g h) = Cmp W Y Z (Cmp W X Y f g) h


-- Notation for the identity map which infers the category:
def identity_map (C : category) (X : C.Obj) := C.Idn X
notation "𝟙_(" C ")" => identity_map C



-- Notation for composition which infers the category and objects:
def composition (C : category) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) : C.Hom X Z := C.Cmp X Y Z f g
notation g "∘_(" C ")" f => composition C f g


theorem Id₁ {C : category} {X : C.Obj} { Y : C.Obj} {f : C.Hom X Y} :
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₂ {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem Ass {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)


macro "cat" : tactic => `(tactic| repeat (rw [Id₁]) ; repeat (rw [Id₂]) ; repeat (rw [Ass]))

example {C : category}
          {W : C.Obj}
          {X : C.Obj}
          {Y : C.Obj}
          {Z : C.Obj}
          {f : C.Hom W X}
          {g : C.Hom X Y}
          {h : C.Hom Y Z}
          {i : C.Hom Z W}:
     (i ∘_(C) (h ∘_(C) (g ∘_(C) (f ∘_(C) (𝟙_(C) W))) ))
  = ((i ∘_(C)  h) ∘_(C) ((𝟙_(C) Y) ∘_(C) g)) ∘_(C) (f) := by cat

ℵᶜᵃᵗ
ᵃ	ᵇ	ᶜ	ᵈ	ᵉ	ᶠ	ᵍ	ʰ	ⁱ	ʲ	ᵏ	ˡ	ᵐ	ⁿ	ᵒ	ᵖ	𐞥	ʳ	ˢ	ᵗ	ᵘ	ᵛ	ʷ	ˣ	ʸ	ᶻ

-- obtaining a morphism from an equality
def Map (C : category) {X : C.Obj} {Y : C.Obj} (p : X = Y) : C.Hom X Y := by
subst p
exact 𝟙_(C) X


notation "Map_(" C ")" p => Map C p


-- definition of an isomorphism from X to Y
structure isomorphism (C : category) (X : C.Obj) (Y : C.Obj) where
  Fst : C.Hom X Y
  Snd : C.Hom Y X
  Id₁ : (C.Cmp X Y X Fst Snd) = C.Idn X
  Id₂ : (C.Cmp Y X Y Snd Fst) = C.Idn Y


-- notation for isomorphisms from X to Y (≅)
notation X "≅_(" C ")" Y => isomorphism C X Y


-- defining the inverse of an isomorphism between objects X and Y
def inverse {C : category} {X : C.Obj} {Y : C.Obj} (f : X ≅_(C) Y) : Y ≅_(C) X := {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}


-- notation for inverse : isos from X to Y to isos from Y to X
notation f "⁻¹" => inverse f


def SetObj := Type

def SetHom (X : SetObj) (Y : SetObj) : Type := X → Y

def SetIdn (X : SetObj) : (SetHom X X) := λ (x : X) => x


def SetCmp (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom X Y) (g : SetHom Y Z) : SetHom X Z := λ (x : X) => (g (f x))


def SetId₁ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X Y Y f (SetIdn Y)) = f := funext (λ _ => rfl)

def SetId₂ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X X Y (SetIdn X) f) = f := rfl

def SetAss (W : SetObj) (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom W X) (g : SetHom X Y) (h : SetHom Y Z) : (SetCmp W X Z f (SetCmp X Y Z g h)) = (SetCmp W Y Z (SetCmp W X Y f g) h) := funext (λ _ => rfl)


def Set : category := {Obj := SetObj, Hom := SetHom, Idn := SetIdn, Cmp := SetCmp, Id₁ := SetId₁, Id₂ := SetId₂, Ass := SetAss}


-- definition of a functor
structure functor (C : category) (D : category) where
   Obj : ∀(_ : C.Obj),D.Obj
   Hom : ∀(X : C.Obj),∀(Y : C.Obj),∀(_ : C.Hom X Y),D.Hom (Obj X) (Obj Y)
   Idn : ∀(X : C.Obj),Hom X X (C.Idn X) = D.Idn (Obj X)
   Cmp : ∀(X : C.Obj),∀(Y : C.Obj),∀(Z : C.Obj),∀(f : C.Hom X Y),∀(g : C.Hom Y Z),
   D.Cmp (Obj X) (Obj Y) (Obj Z) (Hom X Y f) (Hom Y Z g) = Hom X Z (C.Cmp X Y Z f g)


--https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Dependent.20type.20hell.20golfing.20challenge






-- definition of the identity functor on objects
def CatIdnObj (C : category) :=
fun(X : C.Obj)=>
X

-- definition of the identity functor on morphisms
def CatIdnMor (C : category) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
f

-- proving the identity law for the identity functor
def CatIdnIdn (C : category) :=
fun(X : C.Obj)=>
Eq.refl (C.Idn X)

-- proving the compositionality law for the identity functor
def CatIdnCmp (C : category) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
Eq.refl (C.Cmp X Y Z f g)


-- defining the identity functor
def CatIdn (C : category) : functor C C :=
{Obj := CatIdnObj C, Hom := CatIdnMor C, Idn := CatIdnIdn C, Cmp := CatIdnCmp C}


-- defining the composition G ∘_(Cat) F on objects
def CatCmpObj (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
(G.Obj (F.Obj X))

-- defining the composition G ∘_(Cat) F on morphisms
def CatCmpHom (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
(G.Hom) (F.Obj X) (F.Obj Y) (F.Hom X Y f)


-- proving the identity law for the composition G ∘_(Cat) F
def CatCmpIdn (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
Eq.trans (congrArg (G.Hom (F.Obj X) (F.Obj X)) (F.Idn X) ) (G.Idn (F.Obj X))


-- proving the compositionality law for the composition G ∘_(Cat) F
def CatCmpCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
((Eq.trans)
(G.Cmp (F.Obj X) (F.Obj Y) (F.Obj Z) (F.Hom X Y f) (F.Hom Y Z g))
(congrArg (G.Hom  (F.Obj X) (F.Obj Z)) (F.Cmp X Y Z f g)))


-- defining the composition in the category Cat
def CatCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) : functor C E :=
{Obj := CatCmpObj C D E F G, Hom := CatCmpHom C D E F G,Idn := CatCmpIdn C D E F G, Cmp := CatCmpCmp C D E F G}


-- proving Cat.Id₁
def CatId₁ (C : category) (D : category) (F : functor C D) : ((CatCmp C D D) F (CatIdn D) = F) := Eq.refl F

-- Proof of Cat.Id₂
def CatId₂ (C : category) (D : category) (F : functor C D) : ((CatCmp C C D) (CatIdn C) F = F) := Eq.refl F

-- Proof of Cat.Ass
def CatAss (B : category) (C : category) (D : category) (E : category) (F : functor B C) (G : functor C D) (H : functor D E) : (CatCmp B C E F (CatCmp C D E G H) = CatCmp B D E (CatCmp B C D F G) H) :=
Eq.refl (CatCmp B C E F (CatCmp C D E G H))


-- The category of categories
universe u
universe v
def Cat : category := {Obj := category.{u, v}, Hom := functor, Idn := CatIdn, Cmp := CatCmp, Id₁:= CatId₁, Id₂:= CatId₂, Ass := CatAss}


notation "𝟙" X => 𝟙_(Cat) X

notation g "∘" f => g ∘_(Cat) f


-- defining the objects of the CatPrd C D
def CatPrdObj (C : category) (D : category) := (D.Obj) × (C.Obj)

-- defining the morphisms of CatPrd C D
def CatPrdHom (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) := (D.Hom X.1 Y.1) × (C.Hom X.2 Y.2)

-- defining the identity functor on an object in C × D
def CatPrdIdn (C : category) (D : category) (X : CatPrdObj C D) := ((D.Idn X.1),(C.Idn X.2))

-- defining the composition on morphisms in C × D
def CatPrdCmp (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (Z : CatPrdObj C D) (f : CatPrdHom C D X Y) (g : CatPrdHom C D Y Z) : CatPrdHom C D X Z := (D.Cmp X.1 Y.1 Z.1 f.1 g.1, C.Cmp X.2 Y.2 Z.2 f.2 g.2)


-- proving the first identity law for morphisms in C ×_Cat D
theorem CatPrdId₁ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) :
  CatPrdCmp C D X Y Y f (CatPrdIdn C D Y) = f := sorry

-- proving the second identity law for morphisms in C ×_Cat D
theorem CatPrdId₂ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) : CatPrdCmp C D X X Y (CatPrdIdn C D X) f = f := sorry

-- proving associativity for morphisms in C ×_Cat D
theorem CatPrdAss
  (C : category) (D : category)
  (W : CatPrdObj C D) (X : CatPrdObj C D)
  (Y : CatPrdObj C D) (Z : CatPrdObj C D)
  (f : CatPrdHom C D W X) (g : CatPrdHom C D X Y) (h : CatPrdHom C D Y Z) :
  CatPrdCmp C D W X Z f (CatPrdCmp C D X Y Z g h) = CatPrdCmp C D W Y Z (CatPrdCmp C D W X Y f g) h := sorry


-- defining the CatPrd of two categories
def CatPrd (C : category) (D : category) : category := {Obj := CatPrdObj C D, Hom := CatPrdHom C D, Idn := CatPrdIdn C D, Cmp := CatPrdCmp C D, Id₁ := CatPrdId₁ C D, Id₂:= CatPrdId₂ C D, Ass := CatPrdAss C D}


notation:1000  D "×_Cat" C => CatPrd C D


def FunPrdObj
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) :
  (C₁ ×_Cat C₂).Obj → (D₁ ×_Cat D₂).Obj :=
  sorry


def FunPrdHom
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj)
  (f : (C₁ ×_Cat C₂).Hom X Y) :
  ((D₁ ×_Cat D₂).Hom (FunPrdObj F G X) (FunPrdObj F G Y) ) :=
  sorry


def FunPrdIdn
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj) :
  (FunPrdHom F G X X ((C₁ ×_Cat C₂).Idn X))  = ((D₁ ×_Cat D₂).Idn (FunPrdObj F G X)) :=
  sorry


def FunPrdCmp
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj)
  (Z : (C₁ ×_Cat C₂).Obj)
  (f : (C₁ ×_Cat C₂).Hom X Y)
  (g : (C₁ ×_Cat C₂).Hom Y Z) :
  ((D₁ ×_Cat D₂).Cmp (FunPrdObj F G X) (FunPrdObj F G Y) (FunPrdObj F G Z) ((FunPrdHom F G) X Y f) (FunPrdHom F G Y Z g)) = (FunPrdHom F G X Z ((C₁ ×_Cat C₂).Cmp X Y Z f g)) :=
  sorry


def FunPrd
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) :
  Cat.Hom (C₁ ×_Cat C₂) (D₁ ×_Cat D₂) :=
  {Obj := FunPrdObj F G, Hom := FunPrdHom F G, Idn := FunPrdIdn F G, Cmp := FunPrdCmp F G}


notation F "×_Fun" G => FunPrd F G


-- defining the category *_Cat
def PntObj : Type := Unit
def PntHom (_ : PntObj) (_ : PntObj) : Type := Unit
def PntIdn (X : PntObj) : PntHom X X := Unit.unit
def PntCmp (X : PntObj) (Y : PntObj) (Z : PntObj) (_ : PntHom X Y) (_ : PntHom Y Z) : PntHom X Z := Unit.unit
def PntId₁ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X Y Y f (PntIdn Y) = f := Eq.refl f
def PntId₂ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X X Y (PntIdn X) f = f := Eq.refl f
def PntAss (W : PntObj) (X : PntObj) (Y : PntObj) (Z : PntObj) (f : PntHom W X) (g : PntHom X Y) (h : PntHom Y Z) : PntCmp W Y Z (PntCmp W X Y f g) h = PntCmp W X Z f (PntCmp X Y Z g h) := Eq.refl Unit.unit
def Pnt : category := {Obj := PntObj, Hom := PntHom, Idn := PntIdn, Cmp := PntCmp, Id₁ := PntId₁, Id₂ := PntId₂, Ass := PntAss}


-- notation for the category *_Cat
notation "*_Cat" => Pnt

