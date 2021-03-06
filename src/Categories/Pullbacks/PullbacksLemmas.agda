open import Categories

module Categories.Pullbacks.PullbacksLemmas {a b}(X : Cat {a}{b}) where
open import Utilities
open Cat X
open import Categories.Monos X
open import Categories.Pullbacks X

pullbackmonic : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Mono g → 
                (q : Pullback f g) → Mono (Square.h (Pullback.sq q))
pullbackmonic {X}{Y}{Z}{f}{g} p q {A}{f₁}{f₂} r = 
  let open Pullback q
      open Square sq
      open PMap
      m₁ : Square f g
      m₁ = record { 
        W    = A; 
        h    = comp h f₁; 
        k    = comp k f₁; 
        scom = 
          proof 
          comp f (comp h f₁) 
          ≅⟨ sym ass ⟩ 
          comp (comp f h) f₁
          ≅⟨ cong (λ f₃ → comp f₃ f₁) scom ⟩ 
          comp (comp g k) f₁
          ≅⟨ ass ⟩ 
          comp g (comp k f₁) 
          ∎ }
      m₂ : Square f g
      m₂ = record { 
        W    = A; 
        h    = comp h f₂; 
        k    = comp k f₂; 
        scom = 
          proof 
          comp f (comp h f₂) 
          ≅⟨ sym ass ⟩ 
          comp (comp f h) f₂
          ≅⟨ cong (λ f₃ → comp f₃ f₂) scom ⟩ 
          comp (comp g k) f₂
          ≅⟨ ass ⟩ 
          comp g (comp k f₂) 
          ∎} 

      lem : Square.k m₁ ≅ Square.k m₂
      lem = p $
        proof 
        comp g (comp k f₁)
        ≅⟨ sym (Square.scom m₁) ⟩ 
        comp f (comp h f₁)
        ≅⟨ cong (comp f) r ⟩ 
        comp f (comp h f₂)
        ≅⟨ Square.scom m₂ ⟩ 
        comp g (comp k f₂)
        ∎
      u = prop m₁

  in 
     proof 
     f₁ 
     ≅⟨ sym (snd u (record { mor = f₁; prop1 = refl; prop2 = refl })) ⟩ 
     mor (fst u)
     ≅⟨ snd u (record { mor = f₂; prop1 = sym r; prop2 = sym lem}) ⟩ 
     f₂ 
     ∎

monic→pullback : ∀{X Z}{f : Hom X Z} → Mono f → Pullback f f
monic→pullback {X}{Z}{f} p = record { 
  sq = record { W = X; h = iden; k = iden; scom = refl }; 
  prop = λ sq' → (record { 
                    mor = h sq'; 
                    prop1 = idl; 
                    prop2 =
                      proof 
                      comp iden (h sq') 
                      ≅⟨ cong (comp iden) (p (scom sq')) ⟩ 
                      comp iden (k sq')
                      ≅⟨ idl ⟩ 
                      k sq'
                      ∎}) , 
                 (λ u' → 
                      proof 
                      h sq'
                      ≅⟨ sym (prop1 u') ⟩ 
                      comp iden (mor u')
                      ≅⟨ idl ⟩ 
                      mor u'
                      ∎)} 
  where
  open Square
  open PMap

easysquare : ∀{X Z}(f : Hom X Z) → Square f f
easysquare {X}{Z} f  = record { W = X; h = iden; k = iden; scom = refl }

pullback→mono : ∀{X Z}{f : Hom X Z} → 
                ((sq' : Square f f) → 
                 Σ (PMap sq' (easysquare f)) 
                   λ u → (u' : PMap sq' (easysquare f)) → 
                         PMap.mor u ≅  PMap.mor u') → Mono f
pullback→mono {X}{Z}{f} g {A}{f₁}{f₂} r = 
  let m : Square f f
      m = record { W = A; h = f₁; k = f₂; scom = r }
      u = fst (g m)
  in
     proof 
     f₁ 
     ≅⟨ sym (prop1 u) ⟩
     comp iden (mor u) 
     ≅⟨ prop2 u ⟩
     f₂ 
     ∎
  where
  open PMap

open import Categories.Isos X
open Square
open PMap

iso→pullback : ∀{X Y Z}{f : Hom X Z}{g : Hom Y Z} → Iso g → Pullback f g
iso→pullback {X}{Y}{Z}{f}{g} giso = 
  let open Iso giso renaming (inv to g'; rinv to p; linv to q)
  in record { 
  sq = record { 
    W = X;
    h = iden;
    k = comp g' f;
    scom = 
      proof 
      comp f iden 
      ≅⟨ idr ⟩ 
      f 
      ≅⟨ sym idl ⟩ 
      comp iden f 
      ≅⟨ cong (λ h → comp h f) (sym p) ⟩ 
      comp (comp g g') f 
      ≅⟨ ass ⟩ 
      comp g (comp g' f) 
      ∎ }; 
  prop = λ sq' → (record { 
                    mor = h sq'; 
                    prop1 = idl; 
                    prop2 = 
                      proof
                      comp (comp g' f) (h sq') 
                      ≅⟨ ass  ⟩ 
                      comp g' (comp f (h sq')) 
                      ≅⟨ cong (comp g') (scom sq') ⟩ 
                      comp g' (comp g (k sq')) 
                      ≅⟨ sym ass ⟩ 
                      comp (comp g' g) (k sq') 
                      ≅⟨ cong (λ f → comp f (k sq')) q ⟩ 
                      comp iden (k sq') 
                      ≅⟨ idl ⟩ 
                      k sq' 
                      ∎ }) ,
                  (λ u' →                      
                     proof 
                     h sq' 
                     ≅⟨ sym (prop1 u') ⟩ 
                     comp iden (mor u')
                     ≅⟨ idl ⟩ 
                     mor u'  
                     ∎)}
