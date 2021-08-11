{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module Prototype where

open import Agda.Builtin.FromNat
open import Data.Erased
open import Data.Nat using (s≤s; z≤n)
import Data.Nat.Literals as NatLits
open import Data.Integer renaming (ℤ to Int)
import Data.Integer.Literals as IntLits
open import Data.Refinement
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

instance
  _ = NatLits.number
  _ = IntLits.number

-- | Naturals as a refinement over integers.
Nat : Set
Nat = [ z ∈ Int ∣ 0 ≤ z ]

instance
  _ : Number Nat
  _ = record { Constraint = λ n → ⊤; fromNat = λ n → (+ n) , [ +≤+ z≤n ] }

-- | Finite types as a refinement over naturals.
Fin : (n : Nat) → Set
Fin n = [ m ∈ Nat ∣ value m ≤ value n ]

_ : Fin 4
_ = 2 , [ lem ]
  where
    lem : 2 ≤ 4
    lem = solveZ3 -- doesn't work inline
