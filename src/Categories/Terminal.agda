module Categories.Terminal where

open import Utilities
open import Categories
open Cat

record Term {a b} (C : Cat {a}{b}) : Set (suc (a ⊔ b)) where
  field T : Obj C
        t : ∀{X} → Hom C X T
        law : ∀{X}{f : Hom C X T} → t {X} ≅ f

