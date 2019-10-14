module Category where

open import Level
open import Function using (flip)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Cat (n m : Level) : Set (suc (n ⊔ m)) where
  constructor MkCat
  infixr 9 _∘_
  infixl 9 _●_ -- associate to the left because of reversal of the arguments
  infix 10  _[_,_] _[_∘_]

  field
    obj : Set n
    _hom_ : (a b : obj) → Set m

    id : {a : obj} -> a hom a
    _●_  : {a b c : obj}
      -> (a hom b)
      -> (      b hom c)
      -> (a    hom    c)


  _∘_  : {a b c : obj}
    -> (      b hom c)
    -> (a hom b)
    -> (a    hom    c)
  _∘_ g f = _●_ f g

  _[_,_] : obj -> obj -> Set m
  _[_,_] = _hom_

  _[_∘_] : {a b c : obj}
    -> b hom c -> a hom b -> a hom c
  _[_∘_] = _∘_


  _[_●_] : {a b c : obj}
    -> a hom b -> b hom c -> a hom c
  _[_●_] = _●_


  field
    left-id  : {a b : obj} {f : a hom b} → (     f ● id ≡ f)
    right-id : {a b : obj} {f : a hom b} → (id ● f      ≡ f)
    assoc : {a b c d : obj}
      {f : a hom b}
      {g :       b hom c}
      {h :             c hom d}
      → (f ● g) ● h ≡ f ● (g ● h)
    ●-resp-≡ : {a b c : obj} → {f g : a hom b} → {h i : b hom c}
      → f ≡ g
      → h ≡ i
      → (f ● h ≡ g ● i)
  syntax ●-resp-≡ l r = l ⟨●⟩ r

  _⟨●⟩refl : {a b c : obj} {f g : a hom b} {h : b hom c}
    → f ≡ g → f ● h ≡ g ● h
  e ⟨●⟩refl = ●-resp-≡ e refl

  _⟨●⟩refl₂ : {a b c d : obj} {f g : a hom b} {h : b hom c} {i : c hom d}
    → f ≡ g → (f ● h) ● i ≡ (g ● h) ● i
  e ⟨●⟩refl₂ = e ⟨●⟩refl ⟨●⟩refl

  _⟨●⟩refl₃ : {a b c d e : obj} {f g : a hom b} {h : b hom c} {i : c hom d} {j : d hom e}
    → f ≡ g → ((f ● h) ● i) ● j ≡ ((g ● h) ● i) ● j
  e ⟨●⟩refl₃ = e ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl

  _⟨●⟩refl₄ : {a b c d e x : obj} {f g : a hom b} {h : b hom c} {i : c hom d} {j : d hom e} {k : e hom x}
    → f ≡ g → (((f ● h) ● i) ● j) ● k ≡ (((g ● h) ● i) ● j) ● k
  e ⟨●⟩refl₄ = e ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl

  refl⟨●⟩_ : {a b c : obj} {f : a hom b} {g h : b hom c}
    → g ≡ h → f ● g ≡ f ● h
  refl⟨●⟩ e = ●-resp-≡ refl e

  infixl 2 connect
  connect : {a c : obj}
    → (b : obj) → a hom b → b hom c → a hom c
  connect b f g  = f ● g
  syntax connect b f g = f →⟨ b ⟩ g

  infix 1 begin→⟨_⟩_
  begin→⟨_⟩_ : (a : obj) → {b : obj} → a hom b → a hom b
  begin→⟨ a ⟩ f = f

  end∘ : {a : obj} → (b : obj) → a hom b → a hom b
  end∘ b f = f
  syntax end∘ b f = f →⟨ b ⟩end


  record CommutativeSquare {a b c d : obj}
    (f : a hom b)
    (g : b hom d)
    (h : a hom c)
    (i : c hom d)
    : Set m where
    constructor MkCommSq
    field
      eqPaths : f ● g ≡ h ● i


  private
    variable
      a b : obj
      f g h i g' h' i' : a hom b

  glue
    : CommutativeSquare f g h i
    → CommutativeSquare i g' h' i'
    → CommutativeSquare f (g ● g') (h ● h') i'
  glue {f = f} {g = g} {h = h} {i} {g' = g'} {h' = h'} {i' = i'}
    (MkCommSq eqPaths₁) (MkCommSq eqPaths₂)
    = MkCommSq (
      begin
         f ● (g ● g')       ≡⟨ sym assoc ⟩
         (f ● g) ● g'       ≡⟨ cong (λ x → (g' ∘ x)) eqPaths₁ ⟩
         (h ● i) ● g'       ≡⟨ assoc ⟩
         h ● (i ● g')       ≡⟨ cong (λ x → (x ∘ h)) eqPaths₂ ⟩
         h ● (h' ● i')      ≡⟨ sym assoc  ⟩
         (h ● h') ● i'
      ∎
    )
