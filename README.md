# `hegg-patterns`

E-graph rewrite rules for common algebraic identities over common DSL types , for use with [hegg](https://hackage.haskell.org/package/hegg). See that package's documentation for an introduction to 
e-graphs and to `hegg`'s interface.

## Example

Given the type below modeling a free Boolean lattice over `a`, the associated base functor, and
some functions lifting each base functor constructor into a [`Pattern`](https://hackage.haskell.org/package/hegg-0.4.0.0/docs/Data-Equality-Matching-Pattern.html)...

```haskell
{-# LANGUAGE OverloadedStrings #-}
import Data.Equality.Matching.Pattern 
  ( Pattern
  , pat
  )
import Data.Equality.Saturation 
  ( Rewrite ( (:=)
            )
  )
module MyDslDemo where

data Lattice a where
  Val  ∷ a → Lattice a
  Bot  ∷ Lattice a
  Top  ∷ Lattice a
  Meet ∷ Lattice a → Lattice a → Lattice a
  Join ∷ Lattice a → Lattice a → Lattice a
  Comp ∷ Lattice a → Lattice a
  deriving Functor

data LatticeF a b where
  ValF  ∷ a → LatticeF a b
  BotF  ∷ LatticeF a b
  TopF  ∷ LatticeF a b
  MeetF ∷ b → b → LatticeF a b
  JoinF ∷ b → b → LatticeF a b
  CompF ∷ b → LatticeF a b
  deriving Functor

valP ∷ ∀ a. a → Pattern (LatticeF a)
valP = pat . ValF

botP, topP ∷ ∀ a. Pattern (LatticeF a)
botP = pat BotF
topP = pat TopF

compP ∷ ∀ a. Pattern (LatticeF a) → Pattern (LatticeF a)
compP = pat . CompF

meetP, joinP ∷ ∀ a. Pattern (LatticeF a) → Pattern (LatticeF a) → Pattern (LatticeF a)
meetP x y = pat (MeetF x y)
joinP x y = pat (JoinF x y)
```

...then the following functions together construct rewrite rules corresponding to some of the common algebraic
identities that hold of Boolean lattices:

``` haskell

meetUnit, meetComm, joinComm, meetJoinDist, unMeetJoinDist ∷ ∀ analysis a. Rewrite analysis (LatticeF a)
{- | The top element of a bounded lattice is the identity of meet:  /∀ x, ⊤ ∧ x = x/.

'meetUnit' is equivalent to the rewrite rule

> meetP topP "x" := "x"

...reflecting one of the directions of the underlying identity — the "simplifying" one that reduces the
number of nodes in the expression tree.
-}
meetUnit = unit meetP topP "x"

-- | This is the analgous rewrite rule for the identity of `join`.
joinUnit = unit joinP botP "x"



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

-- ...
```

None of the rules here are presently terribly complicated, and rules for essentially only one DSL schema are currently present. Pull requests are welcome.
