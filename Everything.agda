{- A category theory library by James Chapman and Niccolò Veltri -}

module Everything where

open import Utilities

open import Categories
open import Categories.Initial
open import Categories.Terminal

open import Categories.Monos
open import Categories.Epis
open import Categories.Isos
open import Categories.Idems
open import Categories.Sections

open import Categories.Pullbacks
open import Categories.Pullbacks.PullbacksLemmas
open import Categories.Pullbacks.PastingLemmas

open import Functors
open import Naturals

open import Monads
open import Monads.Morphisms
open import Adjunctions
open import Adjunctions.Adj2Mon

open import Monads.Kleisli
open import Monads.Kleisli.Functors
open import Monads.Kleisli.Adjunction

open import Monads.EM
open import Monads.EM.Functors
open import Monads.EM.Adjunction

-- here be dragons
open import Monads.CatofAdj
open import Monads.CatofAdj.InitAdj
open import Monads.CatofAdj.TermAdjHom
open import Monads.CatofAdj.TermAdjObj
open import Monads.CatofAdj.TermAdjUniq
open import Monads.CatofAdj.TermAdj




