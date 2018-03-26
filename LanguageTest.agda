module _ where

open import Agda.Builtin.Equality                using  (_≡_; refl)
open import Data.String              as String   hiding (_==_)
open import Function
open import Data.Maybe               as Maybe    using  (Maybe)
open import Data.Maybe
open import Category.Functor         as Functor  using  (RawFunctor)
open import Text.Parser.Success      as Success

open import Parsers
open import Language

open RawFunctor

-- TODO: all these tests should go in TestParse

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
