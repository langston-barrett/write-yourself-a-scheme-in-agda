module _ where

open import Agda.Builtin.Equality                using (_≡_; refl)
open import Agda.Builtin.Int                     using (pos)
open import Data.Bool                            using  (true ; false)
open import Data.Char                as Char
open import Data.List                            using ([])
open import Data.List.NonEmpty       as NonEmpty using (_∷_; _∷⁺_)
open import Data.List.Sized                      hiding (list)
open import Data.Maybe               as Maybe    using (Maybe ; maybe′)
open import Data.String              as String   hiding (_==_)
open import Relation.Unary.Indexed               using ([_])
open import Text.Parser.Char                     using (spaces)
open import Text.Parser.Combinators              using (Parser ; _&>_ ; box)
open import Text.Parser.Success      as Success

open import Main
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

-- ---------------------------------------------- list

-- Singletons are still treated as non-lists
test₁₀ : fail! list "(asdf)"
test₁₀ = refl
-- test₁₀ : test-parser list "(asdf)" (Util.atom "asdf")
-- test₁₀ = refl

test₁₁ : test-parser list "(f true 10)" (Util.list (Util.atom "f" ∷⁺ (Util.bool true ∷⁺ (Util.integer (pos 10) ∷ []))))
test₁₁ = refl
