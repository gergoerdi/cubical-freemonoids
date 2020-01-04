---
title: Free monoids take a price HIT
author: |
   | Gergő Érdi
   | \url{http://unsafePerform.IO/}
date: Haskell.SG, January 2020.
colortheme: crane
---

# Recap: your grandma's free monoids

## Monoids

<!--
```agda
{-# OPTIONS --cubical --postfix-projections #-}

open import Cubical.Core.Everything renaming (Type to Type′)
open import Cubical.Foundations.Everything hiding (Type; assoc)

Type : Set _
Type = Type₀

variable
  ℓ : Level
  A B C T : Type

infixr 2 _≡⟨⟩_
_≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ p = x ≡⟨ refl ⟩ p

ap : ∀ {B : A → Type} {f g : (x : A) → B x} (p : f ≡ g) → (x : A) → f x ≡ g x
ap p x = cong (λ f → f x) p

id : A → A
id x = x
```
-->

```agda
record Monoid A : Type where
  field
    set : isSet A

    _⋄_ : A → A → A
    ε   : A

    unit-l : ∀ x     → ε ⋄ x ≡ x
    unit-r : ∀ x     → x ⋄ ε ≡ x
    assoc  : ∀ x y z → (x ⋄ y) ⋄ z ≡ x ⋄ (y ⋄ z)

open Monoid {{...}}
```

## Syntax of monoids

```agda
data MonoidSyntax A : Type where
  Element : A → MonoidSyntax A
  _:⋄:_   : MonoidSyntax A → MonoidSyntax A → MonoidSyntax A
  :ε:     : MonoidSyntax A
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
  open Monoid M renaming (_⋄_ to _⋄₁_; ε to ε₁)
  open Monoid N renaming (_⋄_ to _⋄₂_; ε to ε₂)
  field
    map      : A → B
    map-unit : map ε₁ ≡ ε₂
    map-op   : ∀ x y → map (x ⋄₁ y) ≡ map x ⋄₂ map y
```

<!--
```agda
Hom-id : ∀ (M : Monoid A) → Hom M M
Hom-id M = record
  { map = id
  ; map-unit = refl
  ; map-op = λ x y → refl
  }

Hom-comp : ∀ {L : Monoid A} {M : Monoid B} {N : Monoid C} →
  Hom M N → Hom L M → Hom L N
Hom-comp φ ψ = record
  { map = φ .map ∘ ψ .map
  ; map-unit = cong (φ .map) (ψ .map-unit) ∙ φ .map-unit
  ; map-op = λ x y → cong (φ .map) (ψ .map-op x y) ∙ φ .map-op (ψ .map x) (ψ .map y)
  }
  where
  open Hom
```
-->

## Free monoids

```agda
Unique : (A : Type′ ℓ) (P : A → Type) → Type′ _
Unique A P = Σ[ x ∈ A ] Σ[ _ ∈ P x ]
  ∀ (y : A) → P y → y ≡ x
```

<!--
```agda
open import Cubical.Data.Sigma using (ΣPathP)

Unique→IsContr : ∀ (A : Type) (P : A → Type) → (∀ x → isProp (P x)) → Unique A P → isContr (Σ A P)
Unique→IsContr A P PIsProp (x , Px , unique) = (x , Px) , λ { (y , Py) → sym (ΣPathP (unique y Py , r Py Px (unique y Py))) }
  where
    r : isOfHLevelDep 1 P
    r = isOfHLevel→isOfHLevelDep {n = 1} PIsProp
```
-->

```agda
record IsFreeMonoidOver (A : Type) (M₀ : Monoid T) : Type₁ where
  open Hom
  field
    inj : A → T
    free : {{M : Monoid B}} (f : A → B) →
      Unique (Hom M₀ M) (λ φ → φ .map ∘ inj ≡ f)

IsFreeMonoid :
  {F : Type → Type} (FM : ∀ {A} → isSet A → Monoid (F A)) →
  Type₁
IsFreeMonoid {F} FM = ∀ {A} (AIsSet : isSet A) →
  IsFreeMonoidOver A (FM AIsSet)
```

<!--
```agda
module _ {{M : Monoid A}} {{N : Monoid B}} (φ ψ : Hom M N) where
  open Hom

  Hom≡ : φ .map ≡ ψ .map → φ ≡ ψ
  Hom≡ p i = record
    { map = p i
    ; map-unit = isSet→isSet' set map-unit₁ map-unit₂ (ap p ε) (λ _ → ε) i
    ; map-op = λ x y → isSet→isSet' set (map-op₁ x y) (map-op₂ x y) (ap p (x ⋄ y)) (cong₂ _⋄_ (ap p x) (ap p y)) i
    }
    where
    open Hom φ renaming (map to map₁; map-unit to map-unit₁; map-op to map-op₁)
    open Hom ψ renaming (map to map₂; map-unit to map-unit₂; map-op to map-op₂)
```
-->

## `List A` is a free monoid

`_++_` is associative simply because there is no place to hide for a
tree structure in a chain of `_∷_`'s.

<!--
```agda
open import Cubical.Data.List

foldr : (A → B → B) → B → List A → B
foldr f y [] = y
foldr f y (x ∷ xs) = f x (foldr f y xs)
```
-->

```agda
listMonoid : isSet A → Monoid (List A)
listMonoid {A = A} AIsSet = record
  { set = isOfHLevelList 0 AIsSet
  ; _⋄_ = _++_
  ; ε = []
  ; unit-l = λ xs → refl
  ; unit-r = ++-unit-r
  ; assoc = ++-assoc
  }

listIsFree : IsFreeMonoid listMonoid
```

<!--
```agda
listIsFree {A = A} AIsSet = record
  { inj = [_]
  ; free = free
  }
  where
  free : ∀ {B} {{M : Monoid B}} (f : A → B) → Unique (Hom (listMonoid AIsSet) M) _
  free {B = B} {{M}} f = hom , funExt (λ x → unit-r (f x)) , λ φ p → Hom≡ φ hom (funExt (pointwise φ p))
    where
    instance _ = listMonoid AIsSet

    hom : Hom (listMonoid AIsSet) M
    hom = record { map = foldr (λ x → f x ⋄_) ε ; map-unit = refl ; map-op = map-op }
      where
      map-op : (xs ys : List A) →
        foldr (λ x → f x ⋄_) ε (xs ++ ys) ≡ (foldr (λ x → f x ⋄_) ε xs) ⋄ (foldr (λ x → f x ⋄_) ε ys)
      map-op [] ys = sym (unit-l _)
      map-op (x ∷ xs) ys = cong (f x ⋄_) (map-op xs ys) ∙ sym (assoc (f x) _ _)

    module _ φ (p : Hom.map φ ∘ [_] ≡ f)  where
      open Hom hom
      open Hom φ renaming (map to map′; map-unit to map-unit′; map-op to map-op′)

      pointwise : ∀ xs → map′ xs ≡ map xs
      pointwise [] = map-unit′
      pointwise (x ∷ xs) = map-op′ [ x ] xs ∙ cong₂ _⋄_ (λ i → p i x) (pointwise xs)
```
-->

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
data HITMon A : Type where
  ⟨_⟩      : A → HITMon A
  :ε:      : HITMon A
  _:⋄:_    : HITMon A → HITMon A → HITMon A

  :unit-l: : ∀ x      → :ε: :⋄: x ≡ x
  :unit-r: : ∀ x      → x :⋄: :ε: ≡ x
  :assoc:  : ∀ x y z  → (x :⋄: y) :⋄: z ≡ x :⋄: (y :⋄: z)

  trunc    : isSet (HITMon A)
```

<!--
```agda
elimIntoProp : (P : HITMon A → Type) → (∀ x → isProp (P x))
             → (∀ x → P ⟨ x ⟩) → P :ε: → (∀ x y → P x → P y → P (x :⋄: y)) → ∀ x → P x
elimIntoProp P PIsProp P⟨_⟩ Pe P⋄ = go
  where
    go : ∀ x → P x
    go ⟨ x ⟩ = P⟨ x ⟩
    go :ε: = Pe
    go (x :⋄: y) = P⋄ x y (go x) (go y)
    go (:unit-l: x i) = isProp→PathP PIsProp (:unit-l: x) (P⋄ _ _ Pe (go x)) (go x) i
    go (:unit-r: x i) = isProp→PathP PIsProp (:unit-r: x) (P⋄ _ _ (go x) Pe) (go x) i
    go (:assoc: x y z i) = isProp→PathP PIsProp (:assoc: x y z) (P⋄ _ _ (P⋄ _ _ (go x) (go y)) (go z)) (P⋄ _ _ (go x) (P⋄ _ _ (go y) (go z))) i
    go (trunc x y p q i j) = r (go x) (go y) (cong go p) (cong go q) (trunc x y p q) i j
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

      probe : PathP (λ i → PathP (λ j → P (trunc x y p q i j)) (go x) (go y))
        (cong go p)
        (cong go q)
      probe = cong (cong go) (trunc x y p q)

      r : isOfHLevelDep 2 P
      r = isOfHLevel→isOfHLevelDep {n = 2} (λ a → hLevelSuc 1 (P a) (PIsProp a))
```
-->

## `HITMon` is trivially a monoid

```agda
freeMonoid : ∀ A → Monoid (HITMon A)
freeMonoid A = record
  { set = trunc
  ; _⋄_ = _:⋄:_
  ; ε = :ε:
  ; unit-l = :unit-l:
  ; unit-r = :unit-r:
  ; assoc = :assoc:
  }
```

\pause

... and it's also free:

```agda
freeMonoidIsFree : IsFreeMonoid (λ {A} _ → freeMonoid A)
```

<!--
```agda
freeMonoidIsFree {A = A} AIsSet = record
  { inj = ⟨_⟩
  ; free = free
  }
  where
  free : ∀ {B} {{M : Monoid B}} (f : A → B) → Unique (Hom (freeMonoid A) M) _
  free {B = B} {{M}} f = hom , funExt (λ x → refl) , λ φ p → Hom≡ φ hom (funExt (pointwise φ p))
    where
    instance _ = freeMonoid A

    hom : Hom (freeMonoid A) M
    hom = record
      { map = map
      ; map-unit = refl
      ; map-op = λ x y → refl
      }
      where
        map : HITMon A → B
        map ⟨ x ⟩ = f x
        map :ε: = ε
        map (x :⋄: y) = map x ⋄ map y
        map (:unit-l: x i) = unit-l (map x) i
        map (:unit-r: x i) = unit-r (map x) i
        map (:assoc: x y z i) = assoc (map x) (map y) (map z) i
        map (trunc x y p q i j) = set (map x) (map y) (cong map p) (cong map q) i j

    module _ φ (p : Hom.map φ ∘ ⟨_⟩ ≡ f)  where
      open Hom hom
      open Hom φ renaming (map to map′; map-unit to map-unit′; map-op to map-op′)

      pointwise : ∀ x → map′ x ≡ map x
      pointwise = elimIntoProp _ (λ x → set _ _) (ap p)
        map-unit′
        λ x y p q → map-op′ x y ∙ cong₂ _⋄_ p q
```
-->

## `List` vs `HITMon`

The two are isomorphic.

From `List` to `HITMon` we can just go right-associated:

```agda
module ListVsHITMon (AIsSet : isSet A) where
  listIsSet : isSet (List A)
  listIsSet = isOfHLevelList 0 AIsSet

  fromList : List A → HITMon A
  fromList [] = :ε:
  fromList (x ∷ xs) = ⟨ x ⟩ :⋄: fromList xs
```

## `List` vs `HITMon` (cont.)

For the other direction, we map fiat equalities to list equality
proofs:

```agda
  toList : HITMon A → List A
  toList ⟨ x ⟩ = x ∷ []
  toList :ε: = []
  toList (x :⋄: y) = toList x ++ toList y
  toList (:unit-l: x i) = toList x
  toList (:unit-r: x i) = ++-unit-r (toList x) i
  toList (:assoc: x y z i) = ++-assoc
    (toList x) (toList y) (toList z)
    i
  toList (trunc x y p q i j) = listIsSet
    (toList x) (toList y)
    (cong toList p)
    (cong toList q)
    i j
```

## `List` vs `HITMon` (cont.)

These two functions form an isomorphism, which we can lift using
univalence into a type equality:

```
  toList-fromList : ∀ xs → toList (fromList xs) ≡ xs
  fromList-toList : ∀ x → fromList (toList x) ≡ x
```

<!--
```
  toList-fromList [] = refl
  toList-fromList (x ∷ xs) = cong (x ∷_) (toList-fromList xs)

  fromList-toList = elimIntoProp (λ m → fromList (toList m) ≡ m) (λ x → trunc (fromList (toList x)) x)
      (:unit-r: ∘ _)
      refl
      (λ x y p q → sym (fromList-homo (toList x) (toList y)) ∙ cong₂ _:⋄:_ p q)
    where
      fromList-homo : ∀ xs ys → fromList xs :⋄: fromList ys ≡ fromList (xs ++ ys)
      fromList-homo [] ys = :unit-l: (fromList ys)
      fromList-homo (x ∷ xs) ys = :assoc: ⟨ x ⟩ (fromList xs) (fromList ys) ∙ cong (⟨ x ⟩ :⋄:_) (fromList-homo xs ys)
```
-->

```agda
  HITMon≃List : HITMon A ≃ List A
  HITMon≃List = isoToEquiv
    (iso toList fromList toList-fromList fromList-toList)

  HITMon≡List : HITMon A ≡ List A
  HITMon≡List = ua HITMon≃List
```

<!--
## `List` vs `HITMon` (cont.)

This gives us an alternative way to prove that `List A` is a monoid / free monoid:

```
  -- foo : ∀ {A : Type₁} {x y : A} (F : A → Type) (p : x ≡ y) (Fx : F x) → PathP (λ i → F (p i)) Fx (subst F p Fx)
  -- foo {x = x} {y = y} F p Fx = {!!}

  -- M : Monoid (List A)
  -- M = subst Monoid HITMon≡List (freeMonoid A)

  -- p : PathP (λ i → Monoid (HITMon≡List i)) (freeMonoid A) M
  -- p = foo Monoid HITMon≡List (freeMonoid A)

  -- FM : IsFreeMonoidOver A M
  -- FM = transp (λ i → IsFreeMonoidOver A (p i)) i0 (freeMonoidIsFree AIsSet)
```
-->

## **The** free monoid

**All** free monoids over the same base set are isomorphic (and thus
by univalence, equal) so it makes sense to talk about **the** free
monoid.

\pause

\begin{overlayarea}{\textwidth}{0pt}
\only<2>{\includegraphics[width=0.9\textwidth]{./universal.jpg}}
\end{overlayarea}

\pause

Sketch of the proof:

* Suppose we have `M` and `N` free monoids over some `A`, and take the
  homomorphisms `φ : Hom N M` (since `N` is free) and `ψ : Hom M N`
  with `φ ∘ injᴺ ≡ injᴹ` and `ψ ∘ injᴹ ≡ injᴺ`

* We have `φ ∘ ψ : Hom M M`, with `φ ∘ ψ ∘ injᴹ ≡ injᴹ`

* Now since `M` is free, take `ι : Hom M M` with `ι ∘ injᴹ ≡ injᴹ` uniquely.
  This gives `φ ∘ ψ ≡ ι ≡ id` since they all
  satisfy this property. Likewise for `ψ ∘ φ`.

* So `φ` and `ψ` form an isomorphism between `M` and `N`. $\qed$

<!--
```
module UniqueFreeMonoid {M N} {{MM : Monoid M}} {{NN : Monoid N}}
  (AIsSet : isSet A)
  (FM : IsFreeMonoidOver A MM)
  (FN : IsFreeMonoidOver A NN)
  where
  open Hom
  open IsFreeMonoidOver

  module _ {M N} {{MM : Monoid M}} {{NN : Monoid N}}
    (FM : IsFreeMonoidOver A MM) (FN : IsFreeMonoidOver A NN) where
    private
      injᴹ = FM .inj
      injᴺ = FN .inj

      freeᴹᴺ = FM .free injᴺ
      freeᴺᴹ = FN .free injᴹ

      φ = freeᴺᴹ .fst
      φ-prop = freeᴺᴹ .snd .fst

      ψ = freeᴹᴺ .fst
      ψ-prop = freeᴹᴺ .snd .fst

      to : M → N
      to = ψ .map

      from : N → M
      from = φ .map

      idᴹ : Hom MM MM
      idᴹ = Hom-id MM

      φψ : Hom MM MM
      φψ = Hom-comp φ ψ

      φψ-lemma : φψ .map ∘ injᴹ ≡ injᴹ
      φψ-lemma =
        φψ .map ∘ injᴹ ≡⟨⟩
        from ∘ to ∘ injᴹ ≡⟨ cong (from ∘_) ψ-prop ⟩
        from ∘ injᴺ ≡⟨ φ-prop ⟩
        injᴹ ∎

      freeᴹᴹ = FM .free injᴹ
      ι = freeᴹᴹ .fst
      ι-unique = freeᴹᴹ .snd .snd

    roundtrip : from ∘ to ≡ id
    roundtrip =
      from ∘ to  ≡⟨⟩
      φψ .map    ≡⟨ cong map      (ι-unique φψ φψ-lemma) ⟩
      ι .map     ≡⟨ cong map (sym (ι-unique idᴹ refl))   ⟩
      idᴹ .map   ≡⟨⟩
      id ∎

  to : M → N
  to = FM .free (FN .inj) .fst .map

  from : N → M
  from = FN .free (FM .inj) .fst .map

  from-to : ∀ x → from (to x) ≡ x
  from-to = ap (roundtrip FM FN)

  to-from : ∀ x → to (from x) ≡ x
  to-from = ap (roundtrip FN FM)

  M≃N : M ≃ N
  M≃N = isoToEquiv (iso to from to-from from-to)
```
-->
