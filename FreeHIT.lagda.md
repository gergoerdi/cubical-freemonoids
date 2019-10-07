---
title: Free monoids take a price HIT
author: Gergő Érdi \url{http://gergo.erdi.hu/}
date: Haskell.SG, December 2019.
colortheme: crane
---

# Recap: your grandma's free monoids

## Monoids

<!--
```agda
{-# OPTIONS --cubical --postfix-projections #-}

open import Cubical.Core.Everything hiding (Type)
open import Cubical.Foundations.Everything hiding (Type; assoc)

Type : Set _
Type = Type₀

variable
  ℓ ℓ′ : Level
  A B : Type
```
-->

```agda
record Monoid A : Type where
  field
    set : isSet A

    _⋄_ : A → A → A
    e   : A

    unit-l : ∀ x     → e ⋄ x ≡ x
    unit-r : ∀ x     → x ⋄ e ≡ x
    assoc  : ∀ x y z → (x ⋄ y) ⋄ z ≡ x ⋄ (y ⋄ z)
  infixr 20 _⋄_
```

## Syntax of monoids

```agda
data MonoidSyntax A : Type where
  Element : A → MonoidSyntax A
  E : MonoidSyntax A
  _:⋄:_ : MonoidSyntax A → MonoidSyntax A → MonoidSyntax A
```

\pause

### Is `MonoidSyntax` a monoid?

Regardless of the carrier type `A`, this is **not a lawful monoid**;
for example:

    xs ⋄ (ys ⋄ zs) = xs :⋄: (ys :⋄: zs)
    (xs ⋄ ys) ⋄ zs = (xs :⋄: ys) :⋄: zs

\pause
There is too fine a structure!

## Monoid homomorphisms

```agda
record Hom (M : Monoid A) (N : Monoid B) : Type₁ where
  open Monoid M renaming (_⋄_ to _⋄₁_; e to e₁)
  open Monoid N renaming (_⋄_ to _⋄₂_; e to e₂)
  field
    map : A → B
    map-unit : map e₁ ≡ e₂
    map-op : ∀ x y → map (x ⋄₁ y) ≡ map x ⋄₂ map y
```

## Free monoids

```agda
Uniquely : {A : Set ℓ} (x : A) (P : A → Set ℓ′) → Set _
Uniquely {A = A} x P = Σ (P x) λ _ → ∀ (y : A) → P y → y ≡ x

Unique : (A : Set ℓ) (P : A → Set ℓ′) → Set _
Unique A P = Σ[ x ∈ A ] (Σ (P x) (λ _ → ∀ (y : A) → P y → y ≡ x))

open import Cubical.Data.Sigma using (ΣPathP)

foobar : ∀ (A : Set ℓ) (P : A → Set ℓ′) → (∀ x → isProp (P x)) → Unique A P → isContr (Σ A P)
foobar A P PIsProp (x , Px , unique) = (x , Px) , λ { (y , Py) → sym (ΣPathP (unique y Py , r Py Px (unique y Py))) }
  where
    r : isOfHLevelDep 1 P
    r = isOfHLevel→isOfHLevelDep {n = 1} PIsProp

record IsFreeMonoidOver (A : Type) {T : Type} (M₀ : Monoid T) : Type₁ where
  open Hom
  field
    inj : A → T
    hom : (M : Monoid B) (f : A → B) → Hom M₀ M
    free : (M : Monoid B) (f : A → B) → Uniquely (hom M f) λ φ → φ .map ∘ inj ≡ f
    foo : (M : Monoid B) (f : A → B) → isContr (Σ[ φ ∈ Hom M₀ M ] (φ .map ∘ inj ≡ f))

IsFreeMonoid : {F : Type → Type} (FM : ∀ {A} → isSet A → Monoid (F A)) → Type₁
IsFreeMonoid {F} FM = ∀ {A : Type} (AIsSet : isSet A) → IsFreeMonoidOver A (FM AIsSet)
```

## `[a]` is a free monoid

```
open import Cubical.Data.List

foldr : (A → B → B) → B → List A → B
foldr f y [] = y
foldr f y (x ∷ xs) = f x (foldr f y xs)

listMonoid : isSet A → Monoid (List A)
listMonoid {A = A} AIsSet = record
  { set = isOfHLevelList 0 AIsSet
  ; _⋄_ = _++_
  ; e = []
  ; unit-l = λ xs → refl
  ; unit-r = ++-unit-r
  ; assoc = ++-assoc
  }

listIsFree : IsFreeMonoid listMonoid
listIsFree {A = A} AIsSet = record
  { inj = [_]
  ; hom = hom
  ; free = λ M f → hom-inj M f  , unique M f
  ; foo = λ M f → (hom M f , hom-inj M f) , λ { (φ , lifting) i → unique M f φ lifting (~ i) , {!!} }
  }
  where
    hom : ∀ {B} (M : Monoid B) (f : A → B) → Hom (listMonoid AIsSet) M
    hom {B = B} M f = record { map = foldr (λ x → f x ⋄_) e ; map-unit = refl ; map-op = map-op }
      where
      open Monoid M

      map-op : (xs ys : List A) →
        foldr (λ x → f x ⋄_) e (xs ++ ys) ≡ (foldr (λ x → f x ⋄_) e xs) ⋄ (foldr (λ x → f x ⋄_) e ys)
      map-op [] ys = sym (unit-l _)
      map-op (x ∷ xs) ys = cong (f x ⋄_) (map-op xs ys) ∙ sym (assoc (f x) _ _)

    hom-inj : ∀ {B} (M : Monoid B) (f : A → B) → Hom.map (hom M f) ∘ [_] ≡ f
    hom-inj M f = funExt λ x → Monoid.unit-r M (f x)

    unique : (M : Monoid B) (f : A → B) (φ : Hom (listMonoid AIsSet) M) →
      Hom.map φ ∘ [_] ≡ f → φ ≡ hom M f
    unique M f φ lifting = λ i → record
      { map = λ xs → pointwise xs i
      ; map-unit = isSet→isSet' set map-unit (Hom.map-unit (hom M f)) map-unit (λ _ → e) i
      ; map-op = λ xs ys → isSet→isSet' set (map-op xs ys) (Hom.map-op (hom M f) xs ys) (λ i → pointwise (xs ++ ys) i) (λ i → pointwise xs i ⋄ pointwise ys i) i
      }
      where
      open Monoid M
      open Hom φ

      pointwise : ∀ xs → Hom.map φ xs ≡ Hom.map (hom M f) xs
      pointwise [] = map-unit
      pointwise (x ∷ xs) = map-op [ x ] xs ∙ cong₂ _⋄_ (λ i → lifting i x) (pointwise xs)

    foo : (M : Monoid B) (f : A → B) (φ : Hom (listMonoid AIsSet) M) →
      Hom.map φ ∘ [_] ≡ f → Set
    foo M f φ lifting = {!!}
      where
      open Monoid M
      open Hom φ

      bar : ∀ i → (λ x → (map-op [ x ] [] ∙ cong₂ _⋄_ (λ i → lifting i x) map-unit) (~ i)) ≡ f
      bar i = funExt λ x →
        (map-op [ x ] [] ∙ cong₂ _⋄_ (λ i → lifting i x) map-unit) (~ i) ≡⟨ {!!} ⟩
        {!!} ≡⟨ {!!} ⟩
        f x ∎

```

```haskell
instance Monoid [a] where
    mempty = []
    mappend = (++)
inj x = [x]
```

`++` is associative simply because there is no place to hide for a
tree structure in a chain of conses.

\pause

```haskell
hom f [] = mempty
hom f (x:xs) = f x <> hom f xs
```

This is unique by induction on the length of the list.

## The price of free

We had to **think** to come up with the representation `[a]` for the
free monoid, it didn't **follow mechanically** from the definition of
monoids.

\pause

What is a good representation for free...

* commutative monoids? \pause `Map a Nat` \pause
* Abelian groups? \pause `Map a Int` \pause
* Groups?

\pause
\raisebox{-0.8\height}{\includegraphics[width=0.25\textwidth]{./ken.jpg}}"I don't want to be thinking, I want to be HoTT!"

# Free monoids in HoTT

## A HoTT & free monoid

**In a HoTT setting**, we can write a free monoid **without thinking** by
taking the monoid syntax and enriching it with the monoid law-induced
equalities as a **higher inductive type**:

```agda
```

```agda
data FreeMonoid A : Type where
  ⟨_⟩     : A → FreeMonoid A
  ε       : FreeMonoid A
  _:⋄:_   : FreeMonoid A → FreeMonoid A → FreeMonoid A

  unit-l : ∀ x      → ε :⋄: x ≡ x
  unit-r : ∀ x      → x :⋄: ε ≡ x
  assoc  : ∀ x y z  → (x :⋄: y) :⋄: z ≡ x :⋄: (y :⋄: z)

  squash : isSet (FreeMonoid A)

infixr 20 _:⋄:_

elimIntoProp : (P : FreeMonoid A → Type) → (∀ x → isProp (P x))
             → (∀ x → P ⟨ x ⟩) → P ε → (∀ x y → P x → P y → P (x :⋄: y)) → ∀ x → P x
elimIntoProp P PIsProp P⟨_⟩ Pε P⋄ = go
  where
    go : ∀ x → P x
    go ⟨ x ⟩ = P⟨ x ⟩
    go ε = Pε
    go (x :⋄: y) = P⋄ x y (go x) (go y)
    go (unit-l x i) = isProp→PathP PIsProp (unit-l x) (P⋄ _ _ Pε (go x)) (go x) i
    go (unit-r x i) = isProp→PathP PIsProp (unit-r x) (P⋄ _ _ (go x) Pε) (go x) i
    go (assoc x y z i) = isProp→PathP PIsProp (assoc x y z) (P⋄ _ _ (P⋄ _ _ (go x) (go y)) (go z)) (P⋄ _ _ (go x) (P⋄ _ _ (go y) (go z))) i
    go (squash x y p q i j) = r (go x) (go y) (cong go p) (cong go q) (squash x y p q) i j
      where
      --
      --      _____
      --    _/     \_
      --   /        /
      -- go x      go y
      --  |\_     /|
      --  |  \___/ |
      --  |        |
      --  |    ____|
      --  |  _/ p  |\_
      --  | /      | /
      --  x        y
      --   \_    _/
      --     \__/
      --      q
      --
      --

      probe : PathP (λ i → PathP (λ j → P (squash x y p q i j)) (go x) (go y))
        (cong go p)
        (cong go q)
      probe = cong (cong go) (squash x y p q)

      r : isOfHLevelDep 2 P
      r = isOfHLevel→isOfHLevelDep {n = 2} (λ a → hLevelSuc 1 (P a) (PIsProp a))

freeMonoid : ∀ A → Monoid (FreeMonoid A)
freeMonoid A = record
  { set = squash
  ; _⋄_ = _:⋄:_
  ; e = ε
  ; unit-l = unit-l
  ; unit-r = unit-r
  ; assoc = assoc
  }

freeMonoidIsFree : IsFreeMonoid (λ {A} _ → freeMonoid A)
freeMonoidIsFree {A = A} AIsSet = record
  { inj = ⟨_⟩
  ; hom = hom
  ; free = λ M f → (hom-inj M f) , unique M f
  }
  where
    hom : ∀ {B : Type} (M : Monoid B) (f : A → B) → Hom (freeMonoid A) M
    hom {B = B} M f = record
      { map = map
      ; map-unit = refl
      ; map-op = λ x y → refl
      }
      where
        open Monoid M renaming (unit-l to unit-l′; unit-r to unit-r′; assoc to assoc′)

        map : FreeMonoid A → B
        map ⟨ x ⟩ = f x
        map ε = e
        map (x :⋄: y) = map x ⋄ map y
        map (unit-l x i) = unit-l′ (map x) i
        map (unit-r x i) = unit-r′ (map x) i
        map (assoc x y z i) = assoc′ (map x) (map y) (map z) i
        map (squash x y p q i j) = set (map x) (map y) (cong map p) (cong map q) i j

    hom-inj : ∀ (M : Monoid B) (f : A → B) → Hom.map (hom M f) ∘ ⟨_⟩ ≡ f
    hom-inj M f = funExt λ x → refl

    unique : ∀ (M : Monoid B) (f : A → B) (φ : Hom (freeMonoid A) M) →
      Hom.map φ ∘ ⟨_⟩ ≡ f → φ ≡ hom M f
    unique M f φ p = λ i → record
      { map = λ x → pointwise x i
      ; map-unit = isSet→isSet' set map-unit refl map-unit (λ _ → e) i
      ; map-op = λ x y → isSet→isSet' set (map-op x y) refl (λ i → pointwise (x :⋄: y) i) (λ i → pointwise x i ⋄ pointwise y i) i
      }
      where
        open Monoid M
        open Hom φ

        pointwise : ∀ x → Hom.map φ x ≡ Hom.map (hom M f) x
        pointwise = elimIntoProp _ (λ x → set _ _) (λ x i → p i x)
          map-unit
          (λ x y p q → map-op x y ∙ cong₂ _⋄_ p q)


module ListVsFreeMonoid (AIsSet : isSet A) where
  listIsSet : isSet (List A)
  listIsSet = isOfHLevelList 0 AIsSet

  fromList : List A → FreeMonoid A
  fromList [] = ε
  fromList (x ∷ xs) = ⟨ x ⟩ :⋄: fromList xs

  toList : FreeMonoid A → List A
  toList ⟨ x ⟩ = x ∷ []
  toList ε = []
  toList (m₁ :⋄: m₂) = toList m₁ ++ toList m₂
  toList (unit-l m i) = toList m
  toList (unit-r m i) = ++-unit-r (toList m) i
  toList (assoc m₁ m₂ m₃ i) = ++-assoc (toList m₁) (toList m₂) (toList m₃) i
  toList (squash m₁ m₂ p q i j) = listIsSet (toList m₁) (toList m₂) (cong toList p) (cong toList q) i j

  toList-fromList : ∀ xs → toList (fromList xs) ≡ xs
  toList-fromList [] = refl
  toList-fromList (x ∷ xs) = cong (x ∷_) (toList-fromList xs)

  fromList-toList : ∀ m → fromList (toList m) ≡ m
  fromList-toList = elimIntoProp (λ m → fromList (toList m) ≡ m) (λ x → squash (fromList (toList x)) x)
      (unit-r ∘ _)
      refl
      (λ m₁ m₂ p q → sym (fromList-homo (toList m₁) (toList m₂)) ∙ cong₂ _:⋄:_ p q)
    where
      fromList-homo : ∀ xs ys → fromList xs :⋄: fromList ys ≡ fromList (xs ++ ys)
      fromList-homo [] ys = unit-l (fromList ys)
      fromList-homo (x ∷ xs) ys = assoc ⟨ x ⟩ (fromList xs) (fromList ys) ∙ cong (⟨ x ⟩ :⋄:_) (fromList-homo xs ys)

  FreeMonoid≃List : FreeMonoid A ≃ List A
  FreeMonoid≃List = isoToEquiv (iso toList fromList toList-fromList fromList-toList)
```

## Is this really free?

What is free?

```agda
```

```agda
```
