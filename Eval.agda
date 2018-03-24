module Eval where

open import Data.Bool           as Bool      using (not ; if_then_else_)
open import Data.Integer        as Integer   using (ℤ ; _+_ ; _-_)
open import Data.List           as List      using (List ; map ; foldl ; [] ; _∷_)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺)
open import Data.Product                     using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String         as String    using (String ; _==_)
open import Data.Sum            as Sum       using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
                                             renaming (map to map-⊎)
open import Function                         using (_$_ ; _∘_ ; id)
open import Level 

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

-- ----------------- SUM

_<$⊎>_ :  ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
       → (B → C) → A ⊎ B  → A ⊎ C
_<$⊎>_ = λ f → map-⊎ id f

-- Like Haskell's partitionEither
partition : ∀ {a b : Level} {A : Set a} {B : Set b}
          → List (A ⊎ B) → List A × List B
partition = List.foldl (λ acc → [ (λ a → (a ∷ proj₁ acc , proj₂ acc)) ,
                                  (λ b → (proj₁ acc , b ∷ proj₂ acc)) ]′)
                       ([] , [])
                            
-- Like Haskell's sequence, but relies on a pure computation and is less
-- efficient
sequenceᵣ : ∀ {a b : Level} {A : Set a} {B : Set b} → List (A ⊎ B) → A ⊎ (List B)
sequenceᵣ l = sequence-helper (partition l)
  where sequence-helper : ∀ {A B} → List A × List B → A ⊎ (List B)
        sequence-helper (a ∷ as , bs) = inj₁ a
        sequence-helper ([] , bs) = inj₂ bs

-- Unlike sequenceᵣ, this one is not strictly less general than partition.
-- We get a guarantee that the list of Bs is non-empty.
sequenceᵣ⁺ : ∀ {a b : Level} {A : Set a} {B : Set b} → List⁺ (A ⊎ B) → A ⊎ (List⁺ B)
sequenceᵣ⁺ = foldl⁺ [ (λ a _ → inj₁ a) , (λ lst x → (λ hd → hd ∷⁺ lst) <$⊎> x) ]′
                    (λ z → (λ x → [ x ]) <$⊎> z) -- TODO: shorten?

-- ----------------- EVAL

numbers : List Lisp → Error ⊎ List ℤ
numbers = sequenceᵣ ∘ (map cast-integer)

numbers⁺ : List⁺ Lisp → Error ⊎ List⁺ ℤ
numbers⁺ = sequenceᵣ⁺ ∘ (map⁺ cast-integer)

-- Take a binary operation to a variadic operation
int-binop-fold⁺ : (ℤ → ℤ → ℤ) → List⁺ ℤ → ℤ
int-binop-fold⁺ op = foldl⁺ op id

-- Take a binary operation to a variadic operation on Lisp values
int-binop-lisp⁺ : (ℤ → ℤ → ℤ) → List⁺ Lisp → Error ⊎ Lisp
int-binop-lisp⁺ op lst = integer <$⊎> (int-binop-fold⁺ op <$⊎> (numbers⁺ lst) )

apply : String → List⁺ Lisp → Error ⊎ Lisp
apply fun args =
  if      (fun == "+")  then int-binop-lisp⁺ (_+_) args
  else if (fun == "-")  then int-binop-lisp⁺ (_-_) args
  else                       inj₁ $ Error.err-undefined fun

-- Note we utilize the "Size" of Lisp, see Util.
-- enhancement: allow for lists of errors
eval : ∀ {i} → Lisp {i} → Error ⊎ Lisp
eval (quoted x)                     = inj₂ x
eval (atom x)                       = inj₂ $ atom x
eval (list (atom fun ∷ []))         = inj₁ (err-noargs fun) -- this could be avoided
eval (list (atom fun ∷ arg ∷ args)) = apply fun (arg ∷ args)
eval x                              = inj₂ x -- string, int, bool
