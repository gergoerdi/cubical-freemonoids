---
title: Free monoids take a price HIT
author: Gergő Érdi
date: Haskell.SG, December 2019.
colortheme: crane
---

# Syntax of monoids

```haskell
data MonoidSyntax a
    = Element a
    | MEmpty
    | MonoidSyntax a :<> MonoidSyntax a
```

# Is `MonoidSyntax` a monoid?

```haskell
instance Monoid (MonoidSyntax a) where
    mempty = MEmpty
    (<>) = (:<>)
```

Regardless of the carrier type `a`, this is **not a lawful monoid**;
for example:

```haskell
xs <> (ys <> zs) = xs :<> (ys :<> zs)
(xs <> ys) <> zs = (xs :<> ys) :<> zs
```

\pause
There is too fine a structure!

# Monoid homomorphisms

If we have

```haskell
Monoid m, Monoid n
f : m -> n
```

then `f` is a monoid homomorphism iff 

```haskell
f mempty = mempty
``` 

and 

```haskell
f (x <> y) = f x <> f y
```


# Free monoids

```haskell
data FreeMonoid a
instance Monoid (FreeMonoid a)
inj :: a -> FreeMonoid a

hom :: (Monoid m) => (a -> m) -> (FreeMonoid a -> m)
```

s.t. `hom` is the **unique** monoid homomorphism that also has

```haskell
hom f (inj x) = f x
```

# `[a]` is a free monoid

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

# The price of free

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

# A HoTT & free monoid

In a HoTT setting, we can write a free monoid **without thinking** by
taking the monoid syntax and enriching it with the monoid law-induced
equalities as a **higher inductive type**:

```agda
data FreeMonoid (A : Type) : Type where
  [_]  : A → FreeMonoid A
  ε    : FreeMonoid A
  _·_  : FreeMonoid A → FreeMonoid A → FreeMonoid A

  εˡ     : ∀ x      → ε · x ≡ x
  εʳ     : ∀ x      → x · ε ≡ x
  assoc  : ∀ x y z  → (x · y) · z ≡ x · (y · z)

  squash : isSet (FreeMonoid A)
```
