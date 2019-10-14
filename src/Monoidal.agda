{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category

module Monoidal {n m} (cat : Cat n m) where

private
  module cc = Cat cat
  variable n' m' n'' m'' : Level

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open cc hiding (_[_,_])
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_



record Monoidal : Set (n ⊔ m) where
  constructor MkMonoidal

  field
    ⊗ : (cat X cat) Functor cat
    𝟙 : obj


  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = (idFunctor 𝕏 ⊗) ●F ⊗

  [x⊗y]⊗z : (cat X (cat X cat)) Functor cat
  [x⊗y]⊗z = (productAssociatorᵣ ●F (⊗ 𝕏 idFunctor {cat = cat}))  ●F ⊗

  [𝟙⊗x] : cat Functor cat
  [𝟙⊗x] = (constFunctor 𝟙 \/ idFunctor {cat = cat}) ●F (⊗)

  [x⊗𝟙] : cat Functor cat
  [x⊗𝟙] = (idFunctor \/ constFunctor 𝟙) ●F ⊗

  field
    associator  : _≅_ {cat = functorCategory} [x⊗y]⊗z x⊗[y⊗z]
    leftUnitor  : _≅_ {cat = functorCategory} [𝟙⊗x] idFunctor
    rightUnitor : _≅_ {cat = functorCategory} [x⊗𝟙] idFunctor

  infixl 10 _⊗ₒ_ _⊗ₘ_
  _⊗ₒ_ : obj → obj → obj
  _⊗ₒ_ = curry (mapObj ⊗)

  _⊗ₘ_ : {a b c d : obj}
    → a hom b
    → c hom d
    → (a ⊗ₒ c) hom (b ⊗ₒ d)
  f ⊗ₘ g = mapMor ⊗ (f , g)

  -- subscript ₘ stands for "morphism"
  λₘ : {a : obj}
    → (𝟙 ⊗ₒ a) hom  a
  λₘ = η (forward leftUnitor)


  ρₘ : {a : obj}
    → (a ⊗ₒ 𝟙) hom  a
  ρₘ = η (forward rightUnitor)

  αₘ : {a b c : obj}
    → ((a ⊗ₒ b) ⊗ₒ c)
    hom (a ⊗ₒ(b ⊗ₒ c))
  --αₘ = η (forward associator)
  αₘ = let t = η (forward associator) in t

  field
    ▵-identity : {a c : obj}
      → αₘ {a = a} {b = 𝟙} {c = c} ● (id ⊗ₘ λₘ) ≡ ρₘ ⊗ₘ id
