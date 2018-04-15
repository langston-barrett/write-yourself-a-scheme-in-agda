module _ where

open import Agda.Builtin.Equality               using  (_≡_; refl)
open import Category.Functor
open import Category.Monad                      using (RawMonad)
open import Data.Integer           as Integer   using (ℤ)
open import Data.List              as List      using (List ; [] ; _∷_)
open import Data.List.NonEmpty     as NonEmpty
open import Data.Sum               as Sum       using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.String            as String    hiding (_==_ ; show)
open import Function                            using (_$_ ; _∘_ ; id)
open import Level

open import Eval
open import Language
open import Parsers                             hiding (atom ; integer)
open import SumUtil
open import Error

open ℤ

show∘eval∘parse : String → errorOr String
show∘eval∘parse str = show <$> (parse str >>= eval)
  where open RawMonad (monadₗ Error _)

_ : eval (atom "str") ≡ inj₂ (atom "str")
_ = refl

_ : eval (list $ (atom "fun") ∷ []) ≡ inj₁ (err-arity₀ "fun")
_ = refl

_ : eval (list $ (atom "+") ∷ (integer (pos 5)) ∷ ((integer (pos 5)) ∷ [])) ≡
         inj₂ (integer (pos 10))
_ = refl

_ : show∘eval∘parse "(+ 2 2)" ≡ inj₂ "4"
_ = refl

_ : show∘eval∘parse "(= 4 4)" ≡ inj₂ "true"
_ = refl

_ : show∘eval∘parse "(= (+ 2 2) 4)" ≡ inj₂ "true"
_ = refl

_ : show∘eval∘parse "(≤ 2 3 4)" ≡ inj₂ "true"
_ = refl

_ : show∘eval∘parse "(≤ 4 3 4)" ≡ inj₂ "false"
_ = refl

_ : show∘eval∘parse "(if true true false)" ≡ inj₂ "true"
_ = refl

_ : show∘eval∘parse "(if (≤ 2 5) false true)" ≡ inj₂ "false"
_ = refl

_ : show∘eval∘parse "(if (≤ 2 5) true true true)" ≡ inj₂ "false"
_ = refl

-- _ : show∘eval∘parse "(car '(5 2 1))" ≡ inj₂ "5"
-- _ = refl

-- _ : show∘eval∘parse "(cdr '(5 2 1))" ≡ inj₂ "'(2 1)"
-- _ = refl
