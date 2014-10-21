module Functors where

open import Categories
open import Utilities


record Fun {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ c ⊔ b ⊔ d) where
  open Cat
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)

IdF : ∀{a b}(C : Cat {a}{b}) → Fun C C
IdF C = record {OMap = id; HMap = id; fid = refl; fcomp = refl}

open Fun
open Cat

•fid : ∀{a b}{C D E : Cat {a}{b}} (F : Fun D E)(G : Fun C D){X : Obj C} →
       HMap F (HMap G (iden C {X})) ≅ iden E {OMap F (OMap G X)}
•fid {C = C}{D}{E} F G =  
  proof
  HMap F (HMap G (iden C)) 
  ≅⟨ cong (HMap F) (fid G) ⟩
  HMap F (iden D)
  ≅⟨ fid F ⟩ 
  iden E 
  ∎ 

•fcomp : ∀{a b}{C D E : Cat {a}{b}} (F : Fun D E)(G : Fun C D)
  {X Y Z : Obj C} {f : Hom C Y Z}{g : Hom C X Y} →
  (HMap F ∘ HMap G) (comp C f g) 
  ≅ 
  comp E ((HMap F ∘ HMap G) f) ((HMap F ∘ HMap G) g)
•fcomp {C = C}{D}{E} F G {f = f}{g} =
  proof
  HMap F (HMap G (comp C f g)) 
  ≅⟨ cong (HMap F) (fcomp G) ⟩ 
  HMap F (comp D (HMap G f) (HMap G g))
  ≅⟨ fcomp F ⟩ 
  comp E (HMap F (HMap G f))(HMap F (HMap G g)) 
  ∎

_•_ : ∀{a b}{C D E : Cat {a}{b}} → Fun D E → Fun C D → Fun C E
F • G = record {
  OMap  = OMap F ∘ OMap G;
  HMap  = HMap F ∘ HMap G;
  fid   = •fid F G;
  fcomp = •fcomp F G}

Faithful : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Fun C D → Set _
Faithful {C = C} F = ∀{A B}{f g : Hom C A B} → HMap F f ≅ HMap F g → f ≅ g

Full : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Fun C D → Set _
Full {C = C}{D} F = 
  ∀{A B}{f : Hom D (OMap F A) (OMap F B)} → Σ (Hom C A B) λ g → HMap F g ≅ f

-- Equality for functors
FunEq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D} → 
        Fun.OMap F ≅ Fun.OMap G →
        (∀{X Y}(f : Hom C X Y) → Fun.HMap F f ≅ Fun.HMap G f) → F ≅ G
FunEq {C = C}{D}{F}{G} p q = cong₄
  {B = λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
     HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  p
  (iext λ X → iext λ Y → ext q)
  (iext λ X → fixtypes (q (iden C)))
  (iext λ X → iext λ Y → iext λ Z → iext λ f → iext λ g → 
    fixtypes (q (comp C f g)))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 

-- Cat of Cats
CCat : ∀{a b} → Cat
CCat {a}{b} = record {
  Obj  = Cat {a}{b};
  Hom  = Fun;
  iden = λ {C} → IdF C;
  comp = _•_;
  idl  = FunEq refl λ _ → refl;
  idr  = FunEq refl λ _ → refl;
  ass  = FunEq refl λ _ → refl}
