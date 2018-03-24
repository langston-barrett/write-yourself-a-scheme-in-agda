module _ where

open import Agda.Builtin.Equality                using  (_≡_; refl)
open import Agda.Builtin.Int                     using  (pos)
open import Data.Bool                            using  (true ; false)
open import Data.Char                as Char
open import Data.List                            using  ([])
open import Data.List.NonEmpty       as NonEmpty using  (_∷_; _∷⁺_)
open import Data.List.Sized                      hiding (list)
open import Data.Maybe               as Maybe    using  (Maybe ; maybe′)
open import Data.String              as String   hiding (_==_)
open import Function
open import Relation.Unary.Indexed               using  ([_])
open import Text.Parser.Char                     using  (spaces)
open import Text.Parser.Combinators              using  (Parser ; _&>_ ; box)
open import Text.Parser.Success      as Success

open import Util as Util hiding (atom ; integer ; list ; string)
open import Parsers

-- ---------------------------------------------- test functions

-- Test a parser by proving the parser, the input, and the expected value
test-parser :
  ∀ {A} → [ Parser Char (∣List _ ∣≡_) Maybe A ] → String → A → Set
test-parser parser input expected =
  expected ≡ maybe′ Success.value whatever (parseit! parser input)
  where postulate whatever : _

-- This is a version for debugging, because "whatever" isn't informative in an
-- error message.
test-parser′ :
  ∀ {A} → [ Parser Char (∣List _ ∣≡_) Maybe A ] → String → A → A → Set
test-parser′ parser input expected dummy =
  expected ≡ maybe′ Success.value dummy (parseit! parser input)

fail! : ∀ {A} → [ Parser Char (∣List _ ∣≡_) Maybe A ] → String → Set
fail! parser input =
  whatever ≡ maybe′ Success.value whatever (parseit! parser input)
  where postulate whatever : _

-- ---------------------------------------------- combinators

private
  module combinators where
    open import Text.Parser.Combinators

    _ : test-parser (between-parens (box $ exact ' ')) "( )" ' '
    _ = refl

-- ---------------------------------------------- symbol

_ : test-parser symbol "$$@" '$'
_ = refl

_ : test-parser symbol "~@!$" '~'
_ = refl

-- ---------------------------------------------- ??

_ : test-parser (spaces &> box symbol) "    ~" '~'
_ = refl

-- ---------------------------------------------- string

_ : test-parser string "\"str⊕\"" (Util.string "str⊕")
_ = refl

-- fails on wrong quotation
_ : fail! string "str⊕\""
_ = refl

_ : fail! string "\"str⊕"
_ = refl

-- ---------------------------------------------- atom

_ : test-parser atom "true" (bool true)
_ = refl

_ : test-parser atom "t" (Util.atom "t")
_ = refl

_ : fail! atom "9"
_ = refl

_ : test-parser atom "asdf" (Util.atom "asdf")
_ = refl

-- TODO: see https://github.com/gallais/agdarsec/pull/5
_ : test-parser atom "True" (Util.atom "True")
_ = refl

-- ---------------------------------------------- list

-- Singletons are still treated as non-lists
-- TODO
open import Function
open import Text.Parser.Combinators
open import Data.List.NonEmpty hiding ([_])

p : [ Parser Char (∣List Char ∣≡_) Maybe (List⁺ Lisp) ]
p = sepBy maybe-quoted $ box spaces

_ : test-parser list "(5 5)"
                (Util.list (Util.integer (pos 5) ∷⁺ (Util.integer (pos 5) ∷ [])))
_ = refl

_ : test-parser list "(true false)"
                (Util.list (Util.bool true ∷⁺ (Util.bool false ∷ [])))
_ = refl

_ : test-parser list "(f true 10)"
                (Util.list
                  (Util.atom "f" ∷⁺ (Util.bool true ∷⁺ (Util.integer (pos 10) ∷ []))))
_ = refl

-- ---------------------------------------------- expr

_ : test-parser expr "(f true 10)" (Util.list (Util.atom "f" ∷⁺ (Util.bool true ∷⁺ (Util.integer (pos 10) ∷ []))))
_ = refl

_ : test-parser expr "\"str\"" (Util.string "str")
_ = refl

_ : test-parser expr "(false true)" (Util.list (Util.bool false ∷⁺ (Util.bool true ∷ [])))
_ = refl

