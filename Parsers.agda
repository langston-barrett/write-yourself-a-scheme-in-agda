module Parsers where

open import Agda.Builtin.Char                   using (primIsSpace)
open import Category.Monad                      using (RawMonadPlus)
open import Data.Bool               as Bool     using  (not ; if_then_else_)
open import Data.Char               as Char
open import Data.List               as List     hiding ([_] ; _++_)
open import Data.List.NonEmpty      as NonEmpty using (List⁺ ; toList)
open import Data.List.Sized         as Sized    hiding (list; map)
open import Data.Maybe              as Maybe
open import Data.Nat.Properties                 using (n≤1+n)
open import Data.Product                        using (_×_ ; proj₁ ; proj₂)
open import Data.String             as String   using (String ; toList ; _++_)
open import Function                            using (_$_ ; _∘_ ; id ; const)
open import Induction.Nat.Strong                using (fix)
open import Level                               using (zero)
open import Relation.Unary.Indexed              using ([_])
open import Text.Parser.Char
open import Text.Parser.Combinators
open import Text.Parser.Numbers                 using (decimalℤ)
open import Text.Parser.Success     as Success

open import Util                    as Util     hiding (string ; atom ; integer)

-- ----------------- UTIL

instance eqChar = Char._≟_

instance
  plusMaybe : RawMonadPlus {zero} Maybe
  plusMaybe = Maybe.monadPlus

  plusList : RawMonadPlus {zero} List.List
  plusList = List.monadPlus

parseit! : {A B : Set} {M : Set → Set}
         → [ Parser A (∣List Char ∣≡_) M B ]
         → (str : String)
         → M (Success A (∣List Char ∣≡_) B (List.length (String.toList str)))
parseit! parser str =
  runParser parser (n≤1+n _) (Sized.fromList (String.toList str))

-- ----------------- COMBINATORS

many : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
      → [ Parser Char (∣List Char ∣≡_) Maybe String ]
many parser = String.fromList <$> NonEmpty.toList <$> list⁺ parser

-- ----------------- SIMPLE

-- Valid symbols to begin identifiers
symbol : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
symbol = anyOf $ String.toList "!#$%&|*+-/:<=>?@^_~"

-- Anything that isn't a whitespace character
not-space : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
not-space = guard (λ c → not (primIsSpace c)) anyTok

-- A lone double quotation mark
quot : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
quot = exact '"'

-- ----------------- SPECIALIZED

string : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
string =
  fix (Parser _ _ _ _) $
    λ rec → Lisp.string <$> between quot (box quot) (box valid-string)
  where
    -- A valid string is anything not containing a double quote
    valid-string : [ Parser Char (∣List Char ∣≡_) Maybe String ]
    valid-string = many (guard (λ c → not (c == '"')) anyTok)

atom : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
atom =
  fix (Parser Char (∣List Char ∣≡_) Maybe Lisp) $
    λ rec → (λ (str : String) →
               if      (String._==_ str "true")  then Lisp.bool Bool.true
               else if (String._==_ str "false") then Lisp.bool Bool.false
               else                                   Lisp.atom str) <$>
                 head&tail <$> pair
  where
    -- The head of an identifier must be a letter or symbol, after that,
    -- anything (non-whitespace) goes.
    pair : [ Parser Char (∣List Char ∣≡_) Maybe (Char × Maybe String) ]
    pair = (alpha <|> symbol) &?>>= (const $ box $ many $ not-space)
    -- Combine the output of pair into a string
    head&tail : (Char × Maybe String) → String
    head&tail pair =
      String.fromList (proj₁ pair ∷ []) ++ (maybe′ id "" $ proj₂ pair)

integer : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
integer = Util.integer <$> decimalℤ
