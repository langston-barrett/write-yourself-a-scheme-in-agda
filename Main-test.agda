module _ where

open import Agda.Builtin.Equality                using (_≡_; refl)          -- ≡
open import Data.Maybe               as Maybe    using (maybe′)
open import Data.List.Sized         -- Sized instance for List A
open import Text.Parser.Success      as Success
open import Data.String              as String   hiding (_==_)
open import Text.Parser.Char                     using (spaces)
open import Data.Bool                            using  (true ; false)
open import Data.Char                as Char
open import Data.Maybe               as Maybe
open import Text.Parser.Combinators              using (Parser ; _&>_ ; box)
open import Relation.Unary.Indexed               using ([_])

open import Main
open import Util                     as Util     hiding (atom ; string)
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

-- ---------------------------------------------- symbol

test₁ : test-parser symbol "$$@" '$'
test₁ = refl

test₂ : test-parser symbol "~@!$" '~'
test₂ = refl

-- ---------------------------------------------- ??

test₃ : test-parser (spaces &> box symbol) "    ~" '~'
test₃ = refl

-- ---------------------------------------------- string

test₄ : test-parser string "\"str\"" (Util.string "str")
test₄ = refl

-- ---------------------------------------------- atom

test₅ : test-parser atom "true" (bool true)
test₅ = refl

test₆ : test-parser atom "t" (Util.atom "t")
test₆ = refl

test₇ : fail! atom "9"
test₇ = refl

test₈ : test-parser atom "asdf" (Util.atom "asdf")
test₈ = refl

-- TODO: see https://github.com/gallais/agdarsec/pull/5
test₉ : test-parser atom "True" (Util.atom "True")
test₉ = refl
