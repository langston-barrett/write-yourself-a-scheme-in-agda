module Parsers where

open import Agda.Builtin.Char                   using (primIsSpace)
open import Category.Monad                      using (RawMonadPlus)
open import Data.Bool               as Bool     using  (not ; if_then_else_ ; _∨_)
open import Data.Char               as Char
open import Data.List               as List     hiding ([_] ; _++_)
open import Data.List.NonEmpty      as NonEmpty using (List⁺ ; toList)
open import Data.List.Sized         as Sized    hiding (list; map)
open import Data.List.Sized.Interface           using (Sized)
open import Data.Maybe              as Maybe
open import Data.Nat.Properties                 using (n≤1+n)
open import Data.Product                        using (_×_ ; proj₁ ; proj₂)
open import Data.String             as String   using (String ; toList ; _++_)
open import Data.Sum                as Sum      using (_⊎_ ; inj₁ ; inj₂)
open import Function                            using (_$_ ; _∘_ ; id ; const)
open import Induction.Nat.Strong    as Strong   using (fix ; □_ ; extract)
open import Level                               using (zero)
open import Relation.Unary.Indexed              using ([_] ; _⟶_)
open import Size
open import Text.Parser.Char
open import Text.Parser.Combinators
open import Text.Parser.Numbers                 using (decimalℤ)
open import Text.Parser.Success     as Success

open import Error
open import Language as Language hiding (atom ; integer ; list ; quoted ; string)

-- ----------------- UTIL

instance eqChar = Char._≟_

instance
  plusMaybe : RawMonadPlus {zero} Maybe
  plusMaybe = Maybe.monadPlus

  plusList : RawMonadPlus {zero} List.List
  plusList = List.monadPlus

-- Just a version of runParser specialized to strings
parseit! : {A B : Set} {M : Set → Set}
         → [ Parser A (∣List Char ∣≡_) M B ]
         → (str : String)
         → M (Success A (∣List Char ∣≡_) B (List.length (String.toList str)))
parseit! parser str =
  runParser parser (n≤1+n _) (Sized.fromList (String.toList str))

-- ----------------- COMBINATORS

module _ {M : Set → Set} {{𝕄 : RawMonadPlus M}} where
  many : [ Parser Char (∣List Char ∣≡_) M Char ]
        → [ Parser Char (∣List Char ∣≡_) M String ]
  many parser = String.fromList <$> NonEmpty.toList <$> list⁺ parser

-- TODO: add to combinators?

module _ {Tok : Set} {Toks : _} {{𝕊 : Sized Tok Toks}}
    {M : Set → Set} {{𝕄 : RawMonadPlus M}} where

  module _ {A B : Set} where
    sepBy : [ Parser Tok Toks M A ⟶ □ Parser Tok Toks M B
            ⟶ Parser Tok Toks M (List⁺ A) ]
    sepBy pA pB = list⁺ (pA <&? pB)

  -- TODO: https://github.com/agda/agda-stdlib/issues/220#issuecomment-360480024
  -- except : List Tok → [ Parser Tok Toks M Char ]
  -- except toks = guard (λ c → not ∈ toks) anyTok
  --   where
  --     _∈_ : ∀ {l} {A : Set l} → A → (Decidable {A = A} (λ y → x ≡ y)) → A → Bool
  --     _∈_ {_} {_} {dec} x xs = ⌊ any dec (λ y → y ≡ x) ⌋

-- ----------------- SIMPLE

-- Valid symbols to begin identifiers
symbol : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
symbol = anyOf $ String.toList "⊓⊔≤!#$%&|*+-/:<=>?@^_~"
 
-- Anything that isn't a whitespace character
not-space : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
not-space = guard (λ c → not (primIsSpace c)) anyTok

-- Anything that isn't a whitespace character
not-space-or-paren : [ Parser Char (∣List Char ∣≡_) Maybe Char ]
not-space-or-paren = guard (λ c → (not (primIsSpace c)) ∨ (c == ')')) anyTok

-- A parser wedged between two characters, like "", [], (), {}, ``, etc.
between-chars : ∀ {A} → Char → Char → [ □ Parser Char (∣List Char ∣≡_) Maybe A
                                      ⟶ Parser Char _ Maybe A ]
between-chars c₁ c₂ = between (exact c₁) (box $ exact c₂)

-- Something between quote marks
between-quotes : ∀ {A} → [ □ Parser _ _ _ A ⟶ Parser _ _ _ A ]
between-quotes = between-chars '"' '"'

-- Something between parentheses
between-parens : ∀ {A} → [ □ Parser _ _ _ A ⟶ Parser _ _ _ A ]
between-parens = between-chars '(' ')'

-- ----------------- SPECIALIZED

string : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
string =
  fix (Parser _ _ _ _) $
    λ rec → Lisp.string <$> between-quotes (box valid-string)
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
    pair = (alpha <|> symbol) &?>>= (const $ box $ many (alpha <|> symbol))
    -- Combine the output of pair into a string
    head&tail : (Char × Maybe String) → String
    head&tail pair =
      String.fromList (proj₁ pair ∷ []) ++ (maybe′ id "" $ proj₂ pair)

integer : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
integer = Language.integer <$> decimalℤ

-- Basic, unquoted, non-list expressions
base-expr : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
base-expr = integer <|> string <|> atom

-- The above, with possible quotation
maybe-quoted : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
maybe-quoted = base-expr <|> Lisp.quoted <$> (exact '\'' &> (box base-expr))

expr : [ Parser Char (∣List Char ∣≡_) Maybe Lisp ]
expr = fix (Parser Char (∣List Char ∣≡_) Maybe Lisp) $ λ rec →
  maybe-quoted
  <|> Lisp.list <$> between-parens (Strong.map (λ p → sepBy p (box spaces)) rec)

-- The main external interface
parse : String → errorOr Lisp
parse str =
  Sum.map err-parse (Success.value) $ maybe-to-eitherᵣ str (parseit! expr str)
  where maybe-to-eitherᵣ : ∀ {A B} → B → Maybe A → B ⊎ A
        maybe-to-eitherᵣ default = maybe′ inj₂ (inj₁ default)
