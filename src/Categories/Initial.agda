module Categories.Initial where

open import Utilities
open import Categories

open Cat

record Init {a b} (C : Cat {a}{b}) : Set (suc (a ⊔ b)) where
  field I : Obj C
        i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f 
