
module Utilities where

open import Level public
open import Function public
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Unit
open import Level
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public

postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ a → B a}
                {g : ∀ a → B' a} → (∀ a → f a ≅ g a) → f ≅ g

postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ {a} → B a}
                 {g : ∀{a} → B' a} → (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

postulate dext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                 {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ {a a'} → a ≅ a' → f a ≅ g a') → f ≅ g

postulate diext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                  {f : ∀ {a} → B a}{f' : ∀{a'} → B' a'} → 
                  (∀{a a'} → a ≅ a' → f {a} ≅ f' {a'}) → 
                  _≅_ {_}{ {a : A} → B a} f { {a' : A'} → B' a'} f'

cong₃ : ∀{a b c d}{A : Set a}{B : A → Set b}
        {C : ∀ x → B x → Set c }{D : ∀ x y → C x y → Set d}
        (f : ∀ x y z → D x y z)
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

cong₄ : ∀{i j k l m}
        {A : Set i}
        {B : A → Set j}
        {C : (a : A) → B a → Set k}
        {D : (a : A)(b : B a) → C a b → Set l}
        {E : Set m}
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        {d : D a b c}{d' : D a' b' c'} → d ≅ d' → 
        (f : (a : A)(b : B a)(c : C a b) → D a b c → E) → 
        f a b c d ≅ f a' b' c' d'
cong₄ refl refl refl refl f = refl

fcong : ∀{a b}{A : Set a}{B : A → Set b}{f f' : (x : A) → B x}
        (a : A) → f ≅ f' → f a ≅ f' a
fcong a refl = refl

dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {f : (a : A) → B a}{f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong refl refl refl = refl

dicong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
         {f : ∀ {a} → B a}{f' : ∀ {a} → B' a} → {a : A}{a' : A'} → 
         a ≅ a' →  B ≅ B' → 
         (λ {a} → f {a}) ≅ (λ {a} → f' {a}) → 
         f {a} ≅ f' {a'}
dicong refl refl refl = refl

cong' : ∀{a b}{A A' : Set a} → A ≅ A' → 
        {B : A → Set b}{B' : A' → Set b} → B ≅ B' → 
        {f : ∀ a → B a}{f' : ∀ a → B' a} → f ≅ f' → 
        {a : A}{a' : A'} → a ≅ a' → f a ≅ f' a'
cong' refl refl refl refl = refl

icong' : ∀{a b}{A A' : Set a} → A ≅ A' → 
         {B : A → Set b}{B' : A' → Set b} → B ≅ B' → 
         {f : ∀ {a} → B a}{f' : ∀ {a} → B' a} → 
         (λ {a} → f {a}) ≅ (λ {a} → f' {a}) → 
         {a : A}{a' : A'} → a ≅ a' → f {a} ≅ f' {a'}
icong' refl refl refl refl = refl

fixtypes : ∀{i}{A A' A'' A''' : Set i}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} →
           a ≅ a'' → p ≅ q
fixtypes {p = refl} {refl} refl = refl

fixtypes' : ∀{i}{A A' A'' A''' : Set i}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
            {p : a ≅ a'}{q : a'' ≅ a'''} →
            a' ≅ a''' → p ≅ q
fixtypes' {p = refl}{q = refl} refl = refl

stripsubst : ∀{a c}{A : Set a}(C : A → Set c) → 
             {a : A} → (c : C a) → 
             {b : A} → (p : a ≅ b) → 
             subst C p c ≅ c
stripsubst C c refl = refl 

EqR : ∀{a}(A : Set a) → Set (suc a)
EqR {a} A = Σ (Rel A a) (λ R → IsEquivalence R)

record Quotient {a : Level} (A : Set a) (R : EqR A) : Set (suc a) where
  open Σ R renaming (proj₁ to _~_)
  field Q : Set a
        abs : A → Q
        rep : Q → A
        ax1 : (a b : A) → a ~ b → abs a ≅ abs b
        ax2 : (q : Q) → abs (rep q) ≅ q
        ax3 : (a : A) → rep (abs a) ~ a

postulate quot : ∀{a}(A : Set a) (R : EqR A) → Quotient A R

