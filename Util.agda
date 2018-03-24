module Util where

open import Function                            using    (id)
open import Data.List                           using    (List ; _∷_)
open import Data.List.NonEmpty
open import Data.Integer             as Integer using    (ℤ)
open import Data.Bool                as Bool
open import Data.Bool.Show                      renaming (show to Bool-show)
open import Data.String              as String  using    (String ; _++_)
open import Size
-- ----------------- LANGUAGE

-- This datatype has a "size", so that functions like "show" are structurally
-- recursive on their `Size` argument. This is similar to how agdarsec makes
-- sure its parsers are total, they structurally recurse on a "length" argument.
--
-- See: https://agda.readthedocs.io/en/v2.5.3/language/sized-types.html
--
data Lisp {i : Size} : Set where
  atom        : String → Lisp
  bool        : Bool → Lisp
  integer     : ℤ → Lisp
  string      : String → Lisp
  quoted      : ∀ {j : Size< i} → Lisp {j} → Lisp
  list        : ∀ {j : Size< i} → List⁺ (Lisp {j}) → Lisp

show : ∀ {i} → Lisp {i} → String
show (atom s)             = s
show (bool b)             = Bool-show b
show (integer i)          = Integer.show i
show (quoted x)           = "'" ++ show x
show (string x)           = "\"" ++ x ++ "\""
show (list lst) =
  "(" ++ (foldr (λ hd acc → hd ++ " " ++ acc) id (map show lst)) ++ ")"
