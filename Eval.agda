module Eval where

open import Category.Functor
open import Category.Monad
open import Data.Bool           as Bool      hiding (_≟_)
open import Data.Integer        as Integer   using (ℤ ; _≤?_)
open import Data.List           as List      using (List ; map ; foldl ; [] ; _∷_ ; length)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺ ; length to length⁺)
open import Data.String         as String    using (String ; _==_)
open import Data.Sum            as Sum       using (inj₁ ; inj₂ ; [_,_]′)
open import Data.Product        as Product   using (proj₁ ; proj₂ ; _,_ ; _×_)
                                             renaming (map to map-⊎)
open import Function                         using (_$_ ; _∘_ ; id)
open import Level
open import Relation.Nullary.Decidable       using (⌊_⌋)

open import Error
open import Language
open import SumUtil

open Language.Cast renaming (integer to cast-integer)

-- TODO: We can't use a Tree for primitives
-- https://github.com/agda/agda-stdlib/issues/256
-- open import Data.AVL                   as AVL    using (Tree)
-- open StrictTotalOrder
-- primitives : Tree {Key = String}            -- Key
--                   (λ _ → List Lisp → Lisp)  -- Value
--                   (isStrictTotalOrder String.strictTotalOrder)
-- primitives = ?

-- ----------------- COMBINATORS

-- These can be used to more succinctly build primitive functions

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

-- Take a binary function to a variadic operation via foldl⁺
-- This generalizes taking a binary operation to a variadic one,
-- and also taking something like ≤ to its repeated application via
-- transitivity.
-- TODO: when given one argument, these just return it. It should curry!
int-lisp⁺ : ∀ {A : Set} → (A → Lisp) → (A → ℤ → ℤ → A) → (ℤ → (A × ℤ))
              → List⁺ Lisp → errorOr Lisp
int-lisp⁺ wrap f init =
  homogeneous⁺ Cast.integer $
    (inj₂ ∘ wrap ∘ proj₁ ∘ foldl⁺
      (λ pair cur → (f (proj₁ pair) (proj₂ pair) cur , cur )) init)

-- Used to implement +, *, etc.
int-int-lisp⁺ : (ℤ → ℤ → ℤ) → List⁺ Lisp → errorOr Lisp
int-int-lisp⁺ op = int-lisp⁺ integer (λ acc old → op acc) (λ x → (x , x))

-- Used to implement ≤
int-bool-lisp⁺ : (Bool → ℤ → ℤ → Bool) → (ℤ → (Bool × ℤ))
               → List⁺ Lisp → errorOr Lisp
int-bool-lisp⁺ = int-lisp⁺ Lisp.bool

-- ----------------- PRIMITIVES

-- -- Variadic, recursive equality!
equal : ∀ {i} → List⁺ (Lisp {i}) → Bool
equal = proj₁ ∘ foldl⁺ helper (λ lsp → ( true , lsp ))
  where helper : Bool × Lisp → Lisp → Bool × Lisp
        helper (b , lsp₁) lsp₂ = (b ∧ lsp₁ ≟ lsp₂ , lsp₂)

-- Application of a primitive function
apply : String → List⁺ Lisp → errorOr Lisp
apply fun args =
  if      (fun == "+")   then int-int-lisp⁺ (Integer._+_) args
  else if (fun == "-")   then int-int-lisp⁺ (Integer._-_) args
  else if (fun == "*")   then int-int-lisp⁺ (Integer._*_) args
  else if (fun == "⊔") ∨ (fun == "max") then int-int-lisp⁺ (Integer._⊔_) args
  else if (fun == "⊓") ∨ (fun == "min") then int-int-lisp⁺ (Integer._⊓_) args
  else if (fun == "≤") ∨ (fun == "<=")  then
    int-bool-lisp⁺ (λ b x y → b ∧ ⌊ x ≤? y ⌋) (λ x → (true , x)) args
  else if (fun == "=")   then inj₂ $ Lisp.bool $ equal args
  else                       inj₁ $ Error.err-undefined fun

-- ----------------- EVALUATION

-- Note we utilize the "Size" of Lisp, see Util.
-- enhancement: allow for lists of errors
eval : ∀ {i} → Lisp {i} → errorOr Lisp

-- ----------------- IF

eval (list (atom "if" ∷ arg₁ ∷ arg₂ ∷ arg₃ ∷ [])) =
  eval arg₁ >>= λ b → if b ≟ Lisp.bool true then eval arg₂ else eval arg₃
  where open RawMonad (monadₗ Error _)

eval (list (atom "if" ∷ args)) = inj₁ $ err-arity 3 (length args) "if"

-- ----------------- FUNCTIONS

eval (list (atom fun ∷ [])) = inj₁ (err-arity₀ fun)

eval (list (atom fun ∷ arg ∷ args)) =
  (sequenceᵣ⁺ $ map⁺ eval (arg ∷ args)) >>= apply fun
  where open RawMonad (monadₗ Error _)

-- ----------------- ATOMIC

eval x                              = inj₂ x -- string, int, bool, etc.
