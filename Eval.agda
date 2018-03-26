module Eval where

open import Category.Monad
open import Data.Bool           as Bool      hiding (_≟_)
open import Data.Integer        as Integer   using (ℤ ; _+_ ; _-_)
open import Data.List           as List      using (List ; map ; foldl ; [] ; _∷_)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺)
open import Data.String         as String    using (String ; _==_)
open import Data.Sum            as Sum       using (inj₁ ; inj₂ ; [_,_]′)
open import Data.Product        as Product   using (proj₁ ; proj₂ ; _,_ ; _×_)
                                             renaming (map to map-⊎)
open import Function                         using (_$_ ; _∘_ ; id)
open import Level

open import Error
open import Language
open import SumUtil

open Language.Cast renaming (integer to cast-integer)

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

-- ----------------- COMBINATORS

-- Cast two arguments to different types, and apply a binary function
-- enhancement: this could be more universe polymorphic
heterogeneous₂ : ∀ {A : Set} {B : Set}
               → cast A → cast B
               → (A → B → errorOr Lisp) → Lisp → Lisp → errorOr Lisp
heterogeneous₂ {A} {B} cast₁ cast₂ fun v₁ v₂ =
  cast₁ v₁ >>= λ v₁' → cast₂ v₂ >>= λ v₂' → fun v₁' v₂'
  where open RawMonad (monadₗ Error _)

-- Cast two arguments to the same type, and apply a binary function
homogeneous₂ : ∀ {A : Set} → (Lisp → errorOr A)
             → (A → A → errorOr Lisp) → Lisp → Lisp → errorOr Lisp
homogeneous₂ c = heterogeneous₂ c c

-- Cast a variable number of arguments to the same type, apply a variadic function
homogeneous⁺ : ∀ {A : Set} → cast A → (List⁺ A → errorOr Lisp)
             → List⁺ Lisp → errorOr Lisp
homogeneous⁺ {A} c f l = Cast.list⁺ c l >>= f
  where open RawMonad (monadₗ Error _)

-- Take a binary operation to a variadic operation
int-binop-fold⁺ : (ℤ → ℤ → ℤ) → List⁺ ℤ → ℤ
int-binop-fold⁺ op = foldl⁺ op id

-- Take a binary operation to a variadic operation on Lisp values
-- TODO: when given one argument, these just return it. It should curry!
int-binop-lisp⁺ : (ℤ → ℤ → ℤ) → List⁺ Lisp → errorOr Lisp
int-binop-lisp⁺ op =
  homogeneous⁺ Cast.integer (inj₂ ∘ integer ∘ int-binop-fold⁺ op)

-- Variadic, recursive equality!
equal : ∀ {i} → List⁺ (Lisp {i}) → Bool
equal = proj₁ ∘ foldl⁺ helper (λ lsp → ( true , lsp ))
  where helper : Bool × Lisp → Lisp → Bool × Lisp
        helper (b , lsp₁) lsp₂ = (b ∧ lsp₁ ≟ lsp₂ , lsp₂)

apply : String → List⁺ Lisp → errorOr Lisp
apply fun args =
  if      (fun == "+")  then int-binop-lisp⁺ (_+_) args
  else if (fun == "-")  then int-binop-lisp⁺ (_-_) args
  else if (fun == "=")  then inj₂ $ Lisp.bool $ equal args
  else                       inj₁ $ Error.err-undefined fun

-- Note we utilize the "Size" of Lisp, see Util.
-- enhancement: allow for lists of errors
eval : ∀ {i} → Lisp {i} → errorOr Lisp
eval (quoted x)                     = inj₂ x
eval (atom x)                       = inj₂ $ atom x
eval (list (atom fun ∷ []))         = inj₁ (err-noargs fun) -- this could be avoided
eval (list (atom fun ∷ arg ∷ args)) = apply fun (arg ∷ args)
eval x                              = inj₂ x -- string, int, bool
