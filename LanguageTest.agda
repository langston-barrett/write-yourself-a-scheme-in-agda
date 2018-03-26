module _ where

open import Agda.Builtin.Equality                using  (_≡_; refl)
open import Data.String              as String   hiding (_==_ ; _≟_)
open import Data.Bool                as Bool     using  (true ; false)
open import Function
open import Data.Maybe               as Maybe    using  (Maybe)
open import Data.Maybe
open import Category.Functor         as Functor  using  (RawFunctor)
open import Text.Parser.Success      as Success

open import Parsers
open import Language

open RawFunctor

-- TODO: all these tests should go in TestParse

-- ----------------- SHOW

-- parse something, then show it
show∘parse : String → Maybe String
show∘parse args =
  RawFunctor._<$>_
    Maybe.functor
    (Language.show ∘ Success.value) (Parsers.parseit! Parsers.expr args)

-- make sure show∘parse = id
test-show∘parse : String → Set
test-show∘parse str = Maybe.just str ≡ show∘parse str

-- atom
_ : test-show∘parse "x"
_ = refl

-- string
_ : test-show∘parse "\"string\""
_ = refl

-- quoted
_ : test-show∘parse "'quoted"
_ = refl

-- integer: TODO this takes forever?
_ : test-show∘parse "1234"
_ = refl

-- list
_ : test-show∘parse "(true false)"
_ = refl

-- ----------------- EQUALITY

-- These tests take a long time for some reason

test-equal-refl : Lisp → Set
test-equal-refl l = (l ≟ l) ≡ true

_ : test-equal-refl (Lisp.bool true)
_ = refl

_ : test-equal-refl (Lisp.bool false)
_ = refl

_ : test-equal-refl (Lisp.string "")
_ = refl

_ : test-equal-refl (Lisp.atom "")
_ = refl
