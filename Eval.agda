module Eval where

open import Data.Bool           as Bool      using (not ; if_then_else_)
open import Data.Integer        as Integer   using (ℤ ; _+_ ; _-_)
open import Data.List           as List      using (List ; map ; foldl ; [] ; _∷_)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺)
open import Data.String         as String    using (String ; _==_)
open import Data.Sum            as Sum       using (inj₁ ; inj₂ ; [_,_]′)
                                             renaming (map to map-⊎)
open import Function                         using (_$_ ; _∘_ ; id)
open import Level 

open import SumUtil
open import Util

open Util.Cast renaming (integer to cast-integer)

-- TODO: the code in this file is simplified by a monad instance for Sum
-- https://github.com/agda/agda-stdlib/pull/221

-- TODO: We can't use a Tree for primitives
-- https://github.com/agda/agda-stdlib/issues/256
-- open import Data.AVL                   as AVL    using (Tree)
-- open StrictTotalOrder
-- primitives : Tree {Key = String}            -- Key
--                   (λ _ → List Lisp → Lisp)  -- Value
--                   (isStrictTotalOrder String.strictTotalOrder)
-- primitives = ?

numbers : List Lisp → errorOr (List ℤ)
numbers = sequenceᵣ ∘ (map cast-integer)

numbers⁺ : List⁺ Lisp → errorOr (List⁺ ℤ)
numbers⁺ = sequenceᵣ⁺ ∘ (map⁺ cast-integer)

-- Take a binary operation to a variadic operation
int-binop-fold⁺ : (ℤ → ℤ → ℤ) → List⁺ ℤ → ℤ
int-binop-fold⁺ op = foldl⁺ op id

-- Take a binary operation to a variadic operation on Lisp values
-- TODO: when given one argument, these just return it. It should curry!
int-binop-lisp⁺ : (ℤ → ℤ → ℤ) → List⁺ Lisp → errorOr Lisp
int-binop-lisp⁺ op lst = integer <$⊎> (int-binop-fold⁺ op <$⊎> (numbers⁺ lst) )

apply : String → List⁺ Lisp → errorOr Lisp
apply fun args =
  if      (fun == "+")  then int-binop-lisp⁺ (_+_) args
  else if (fun == "-")  then int-binop-lisp⁺ (_-_) args
  else                       inj₁ $ Error.err-undefined fun

-- Note we utilize the "Size" of Lisp, see Util.
-- enhancement: allow for lists of errors
eval : ∀ {i} → Lisp {i} → errorOr Lisp
eval (quoted x)                     = inj₂ x
eval (atom x)                       = inj₂ $ atom x
eval (list (atom fun ∷ []))         = inj₁ (err-noargs fun) -- this could be avoided
eval (list (atom fun ∷ arg ∷ args)) = apply fun (arg ∷ args)
eval x                              = inj₂ x -- string, int, bool
