{-# OPTIONS_HADDOCK show-extensions #-}
{- | Functions for constructing rewriting rules for common algebraic identities against typical initial
encodings of DSLs.

== Example

Given the type below modeling a free Boolean lattice over @a@, the associated base functor, and
some functions lifting each base functor constructor into a 'Pattern'...

@
import Data.Equality.Matching.Pattern
  ( Pattern
  , pat
  )
import Data.Equality.Saturation
  ( Rewrite ( (:=)
            )
  )

-- A sample of the rewrites provided by this package:
import Data.Equality.Matching.Pattern.Extras
  ( unit
  , zero
  , comm
  , dist
  , unDist
  )


data Lattice a where
  Val  :: a -> Lattice a
  Bot  :: Lattice a
  Top  :: Lattice a
  Meet :: Lattice a -> Lattice a -> Lattice a
  Join :: Lattice a -> Lattice a -> Lattice a
  Comp :: Lattice a -> Lattice a
  deriving Functor

data LatticeF a b where
  ValF  :: a -> LatticeF a b
  BotF  :: LatticeF a b
  TopF  :: LatticeF a b
  MeetF :: b -> b -> LatticeF a b
  JoinF :: b -> b -> LatticeF a b
  CompF :: b -> LatticeF a b
  deriving Functor

valP :: forall a. a -> Pattern (LatticeF a)
valP = pat . ValF

botP, topP :: forall a. Pattern (LatticeF a)
botP = pat BotF
topP = pat TopF

compP :: forall a. Pattern (LatticeF a) -> Pattern (LatticeF a)
compP = pat . CompF

meetP, joinP :: forall a. Pattern (LatticeF a) -> Pattern (LatticeF a) -> Pattern (LatticeF a)
meetP x y = pat (MeetF x y)
joinP x y = pat (JoinF x y)
@

...then the following functions use a few functions from this module to construct rewrite rules corresponding to
some of the common algebraic identities that hold of Boolean lattices:

@
meetUnit, meetZero, meetComm, joinComm, meetJoinDist :: forall analysis a. Rewrite analysis (LatticeF a)
{- | The top element of a bounded lattice is the identity of meet:  /∀ x, ⊤ ∧ x = x/.

'meetUnit' is equivalent to the rewrite rule

> meetP topP "x" := "x"

...reflecting one of the directions of the underlying identity — the "simplifying" one that reduces the
number of nodes in the expression tree.
-}
meetUnit = unit meetP topP "x"

-- | This is the analgous rewrite rule for the identity of `join`.
joinUnit = unit joinP botP "x"

{- | The bottom element of a bounded lattice is the absorbing element (zero) of meet: 'meetZero' creates
the rewrite rule

> meetP botP "x" := botP
-}
meetZero = zero meetP botP "x"

-- | This is the analgous rewrite rule for the absorbing element of `join`.
joinZero = zero joinP topP "x"

{- | Meet is commutative. Equivalent to

> meetP "x" y := meetP "y" "x"

-}
meetComm = comm meetP "x" "y"

-- | Join is also commutative...
joinComm = comm joinP "x" "y"

{- | This rule creates one of the two directions of the identity reflecting that /meet distributes over join/.

> "x" `meetP` ("y" `joinP` "z") := ("x" `meetP` "y") `joinP` ("x" `meetP` "z")
-}
meetJoinDist = dist meetP joinP "x" "y" "z"

-- | This rule generates the other direction of the /meet-distributes-over-join/ identity.
unMeetJoinDist = unDist meetP joinP "x" "y" "z"

@

-}

module Data.Equality.Matching.Pattern.Extras
  ( -- * Identity elements
    unitL
  , unUnitL
  , unitR
  , unUnitR
  , unit
  , unUnit

    -- * Absorbing (annihilating) elements
  , zeroL
  , unZeroL
  , zeroR
  , unZeroR
  , zero
  , unZero

  , zeroSelf

    -- * Idempotency
  , idem
  , idem'

    -- * Commutativity
  , comm

    -- * Associativity
  , assocL
  , assocR

    -- * Distributivity
  , distL
  , unDistL
  , distR
  , unDistR
  , dist
  , unDist

  , distIn
  , unDistIn

    -- * Involution
  , inv

    -- * Fixpoints
  , fix
  ) where

import Data.Equality.Matching.Pattern
  ( Pattern
  )

import Data.Equality.Saturation.Rewrites
  ( Rewrite ( (:=)
            )
  )


{- | @unitL opP uP xP@ creates a rule expressing the simplification @u \`op\` x@ → @x@.

__Example__

Continuing the lattice example, a variable pattern as the final argument in
@unitL meetP topP "x"@ captures the left-to-right reduction associated with

 - /∀ x, ⊤ ∧ x = x/

I.e., expressing that 'Top' is the left identity of meet for any possible term.

> unitL meetP topP "x" ≡ meetP topP "x" := "x"
-}
unitL ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ left identity
  → Pattern lang
  → Rewrite analysis lang
unitL f u x = f u x
           := x
{-# INLINABLE unitL #-}

{- | Inverse rule of 'unitL': @unInitL opP uP xP@ creates a rule expressing the expansion
@x@ → @u \`op\` x@.

> unUnitL meetP topP "x" ≡ "x" := meetP topP "x"  -- ∀ x, ⊤ ∧ x = x
-}
unUnitL ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Left identity element
  → Pattern lang
  → Rewrite analysis lang
unUnitL f u x = x
             := f u x
{-# INLINABLE unUnitL #-}

{- | Right-identity analogue of 'unitL': @unitR opP uP xP@ creates a rule expressing the simplification of
@x \`op\` u@ to @x@.

> unitR meetP topP "x" ≡ meetP "x" topP := "x"  -- ∀ x, x ∧ ⊤ = x
-}
unitR ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Right identity element
  → Pattern lang
  → Rewrite analysis lang
unitR f u x = f x u
           := x
{-# INLINABLE unitR #-}

{- | Right-identity analogue of 'unUnitL': @unUnitR opP uP xP@ creates a rule expressing the expansion of
@x@ to @x \`op\` u@.

> unUnitR meetP topP "x" ≡ "x" := meetP "x" topP  -- ∀ x, x ∧ ⊤ = x
-}
unUnitR ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Right identity element
  → Pattern lang
  → Rewrite analysis lang
unUnitR f u x = x
             := f x u
{-# INLINABLE unUnitR #-}

{- | Synonym for 'unitL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
unit ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Identity element
  → Pattern lang
  → Rewrite analysis lang
unit = unitL
{-# INLINABLE unit #-}

{- | Synonym for 'unUnitL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
unUnit ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Identity element
  → Pattern lang
  → Rewrite analysis lang
unUnit = unUnitL
{-# INLINABLE unUnit #-}



{- | @zeroL opP zP xP@ creates a rule expressing the simplification of @z \`op\` x@ to @z@.

> zeroL meetP botP "x" ≡ meetP botP "x" := "x"  -- ∀ x, ⊥ ∧ x = ⊥
-}
zeroL ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Left absorbing element
  → Pattern lang
  → Rewrite analysis lang
zeroL f z x = f z x
           := z
{-# INLINABLE zeroL #-}

{- | @unZeroL opP zP xP@ creates a rule expressing the expansion of @z@ to @z \`op\` x@.

> unZeroL meetP botP "x" ≡ "x" := meetP botP "x"  -- ∀ x, ⊥ ∧ x = ⊥
-}
unZeroL ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Left absorbing element
  → Pattern lang
  → Rewrite analysis lang
unZeroL f z x = z
             := f z x
{-# INLINABLE unZeroL #-}

{- | @zeroR opP zP@ creates a rule expressing the simplification of @x \`op\` z@ to @z@.

> zeroR meetP botP "x" ≡ meetP "x" botP := "x"  -- ∀ x, x ∧ ⊥ = ⊥
-}
zeroR ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Right absorbing element
  → Pattern lang
  → Rewrite analysis lang
zeroR f z x = f x z
           := z
{-# INLINABLE zeroR #-}

{- | @unZeroR op zP xP@ creates a rule expressing the expansion of @z@ to @z \`op\` x@.

> unZeroR meetP botP "x" ≡ "x" := meetP "x" botP  -- ∀ x, x ∧ ⊥ = ⊥
-}
unZeroR ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Right absorbing element
  → Pattern lang
  → Rewrite analysis lang
unZeroR f z x = z
             := f x z
{-# INLINABLE unZeroR #-}

{- | Synonym for 'zeroL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
zero ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Absorbing element
  → Pattern lang
  → Rewrite analysis lang
zero = zeroL
{-# INLINABLE zero #-}

{- | Synonym for 'unZeroL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
unZero ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Absorbing element
  → Pattern lang
  → Rewrite analysis lang
unZero = unZeroL
{-# INLINABLE unZero #-}

{- | @zeroSelf opP zP xP@ creates a rule expressing the simplification of @x \`op\` x@ to @z@, asserting that
every @x@ is its own annihilator (absorbing element) under @op@.

> zeroSelf minusP zeroP "x" ≡ minusP "x" "x" := zeroP  -- ∀ x ∈ ℕ, x - x = 0
-}
zeroSelf ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang  -- ^ Absorbing element
  → Pattern lang
  → Rewrite analysis lang
zeroSelf f z x = (x `f` x)
              := z
{-# INLINABLE zeroSelf #-}





{- | Create a rule expressing the simplification of @f (f x)@ to @f x@.

> idem absValP "x" ≡ absValP (absValP "x") := absValP "x"  -- ∀ x ∈ ℤ, ||x|| = |x|
-}
idem ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang)  -- ^ Constructor representing a unary operation
  → Pattern lang
  → Rewrite analysis lang
idem f x = f (f x)
        := f x
{-# INLINABLE idem #-}

{- | Create a rule expressing the simplification of @x \`op\` x@ to @x@.

> idem' meetP "x" ≡ meetP "x" "x" := "x"  -- ∀ x, x ∧ x = x
-}
idem' ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang
  → Rewrite analysis lang
idem' f x = (x `f` x)
         := x
{-# INLINABLE idem' #-}




{- | Create a rule asserting commutativity.

> comm meetP "x" "y" ≡ meetP "x" "y" := meetP "y" "x"  -- ∀ x, y, x ∧ y = y ∧ x
-}
comm ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang
  → Pattern lang
  → Rewrite analysis lang
comm f l r = f l r
          := f r l
{-# INLINABLE comm #-}

{- | Create a rule that reassociates rightwards: @(x \`op\` y) \`op\` z@ becomes @x \`op\` (y \`op\` z)@.

> assocR meetP "x" "y" "z" ≡ meetP (meetP "x" "y") "z" := meetP "x" (meetP "y" "z")  -- ∀ x, y, z, (x ∧ y) ∧ z = x ∧ (y ∧ z)
-}
assocR ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang
  → Pattern lang
  → Pattern lang
  → Rewrite analysis lang
assocR f x y z = f (f x y) z
              := f x (f y z)
{-# INLINABLE assocR #-}

{- | Create a rule that reassociates leftwards: @x \`op\` (y \`op\` z)@ becomes @(x \`op\` y) \`op\` z@.

> assocL meetP "x" "y" "z" ≡ meetP "x" (meetP "y" "z") := meetP (meetP "x" "y") "z"  -- ∀ x, y, z, (x ∧ y) ∧ z = x ∧ (y ∧ z)
-}
assocL ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  → Pattern lang
  → Pattern lang
  → Pattern lang
  → Rewrite analysis lang
assocL f x y z = f x (f y z)
              := f (f x y) z
{-# INLINABLE assocL #-}



{- | @distL fP gP "x" "y"@ creates a rule distributing @f@ over @g@ from the left:
@x `f` (y `g` z)@ becomes @(x `f` y) `g` (x `f` z)@.

> distL meetP joinP "x" "y" "z" ≡ "x" `meetP` ("y" `joinP` "z") := ("x" `meetP` "y") `joinP` ("x" `meetP` "z")
-}
distL ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation distributing inwards
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation distributed over
  →  Pattern lang  -- ^ Leftmost ("outside") term before application of the rule
  →  Pattern lang
  →  Pattern lang
  →  Rewrite analysis lang
distL f g x y z = x `f` (y `g` z)
               := (x `f` y) `g` (x `f` z)
{-# INLINABLE distL #-}

{- | Create a rule that is the inverse of the analogous 'distL' call:

> unDistL meetP joinP "x" "y" "z" ≡ ("x" `meetP` "y") `joinP` ("x" `meetP` "z") := "x" `meetP` ("y" `joinP` "z")
-}
unDistL ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation to undistribute
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  →  Pattern lang  -- ^ Leftmost ("outside") after application of the rule
  →  Pattern lang
  →  Pattern lang
  →  Rewrite analysis lang
unDistL f g x y z = (x `f` y) `g` (x `f` z)
                 := x `f` (y `g` z)
{-# INLINABLE unDistL #-}

{- | @distR fP gP "x" "y" "z"@ creates a rule distributing @f@ over @g@ from the right:
@(x `g` y) `f` z@ becomes @(x `f` z) `g` (y `f` z)@.

> distR meetP joinP "x" "y" "z" ≡ ("x" `joinP` "y") `meetP` "z" := ("x" `meetP` "z") `joinP` ("y" `meetP` "z")
-}
distR ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation distributing inwards
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation distributed over
  →  Pattern lang
  →  Pattern lang
  →  Pattern lang  -- ^ Rightmost ("outside") term before application of the rule
  →  Rewrite analysis lang
distR f g x y z = (x `g` y) `f` z
               := (x `f` z) `g` (y `f` z)
{-# INLINABLE distR #-}

{- | Create a rule that is the inverse of the analogous 'distR' call:

> unDistR meetP joinP "x" "y" "z" ≡ ("x" `meetP` "z") `joinP` ("y" `meetP` "z") := ("x" `joinP` "y") `meetP` "z"
-}
unDistR ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation to undistribute
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation
  →  Pattern lang
  →  Pattern lang
  →  Pattern lang  -- ^ Rightmost ("outside") term after application of the rule
  →  Rewrite analysis lang
unDistR f g x y z = (x `f` z) `g` (y `f` z)
                 := (x `g` y) `f` z
{-# INLINABLE unDistR #-}

{- | Synonym for 'distL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
dist ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)
  → (Pattern lang → Pattern lang → Pattern lang)
  →  Pattern lang
  →  Pattern lang
  →  Pattern lang
  →  Rewrite analysis lang
dist = distL
{-# INLINABLE dist #-}

{- | Synonym for 'unDistL' for use in contexts where the operation is commutative (and some other rewrite
rule has declared as much). -}
unDist ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang → Pattern lang)
  → (Pattern lang → Pattern lang → Pattern lang)
  →  Pattern lang
  →  Pattern lang
  →  Pattern lang
  →  Rewrite analysis lang
unDist = unDistL
{-# INLINABLE unDist #-}


-- TODO find a concrete example
{- | Crate a rule that distributes a unary operation over a binary one:
@f (x \`op\` y)@ becomes @f x \`op\` f y@.

> distIn fP opP "x" "y" ≡ fP ("x" `opP` "y") := (fP "x") `opP` (fP "y")
-}
distIn ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang)  -- ^ Constructor representing a unary operation to distribute inwards
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation to distribute into
  → Pattern lang
  → Pattern lang
  → Rewrite analysis lang
distIn f op l r = f (l `op` r)
               := f l `op` f r
{-# INLINABLE distIn #-}

{- | Create a rule that is the inverse of the analogous 'distIn' call:
@f x \`op\` f y@ becomes @f (x \`op\` y)@.

> unDistIn fP opP "x" "y" ≡ (fP "x") `opP` (fP "y") := fP ("x" `opP` "y")
-}
unDistIn ∷ ∀ analysis lang.
    (Pattern lang → Pattern lang)  -- ^ Constructor representing a unary operation to undistribute
  → (Pattern lang → Pattern lang → Pattern lang)  -- ^ Constructor representing a binary operation to distribute out of
  →  Pattern lang
  →  Pattern lang
  →  Rewrite analysis lang
unDistIn f op l r = f l  `op` f r
                 := f (l `op` r)
{-# INLINABLE unDistIn #-}



{- | Create a rule expressing the simplification of an operation that is an involution: @f (f x)@ becomes @x@.

> inv fP "x" ≡ fP (fP "x") := fP "x"
-}
inv ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang)
  → Pattern lang
  → Rewrite analysis lang
inv f x = f (f x)
       := x
{-# INLINABLE inv #-}



{- | Create a rule asserting that a particular pattern is a fixpoint of an operation: @f x@ becomes @x@.

> fix absP zeroP ≡ absP zeroP := zeroP  -- |0| = 0
-}
fix ∷ ∀ analysis lang.
   (Pattern lang → Pattern lang)
  → Pattern lang
  → Rewrite analysis lang
fix f x = f x
       := x
{-# INLINABLE fix #-}
