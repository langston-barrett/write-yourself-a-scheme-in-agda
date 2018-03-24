module Util where

open import Function                            using    (id)
open import Data.List                           using    (List ; _∷_)
open import Data.List.NonEmpty
open import Data.Integer             as Integer using    (ℤ)
open import Data.Bool                as Bool
open import Data.Bool.Show                      renaming (show to Bool-show)
open import Data.String              as String  using    (String ; _++_)
open import Data.Sum                 as Sum     using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Size

-- ----------------- LANGUAGE

-- We put this in its own module so that we can redefine things like
-- "bool" and "integer" within other modules. We re-export it at the end of the
-- file.
module LispM where

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
    -- enhancement this should be made into vectors of length > 1
    list        : ∀ {j : Size< i} → List⁺ (Lisp {j}) → Lisp

  show : ∀ {i} → Lisp {i} → String
  show (atom s)             = s
  show (bool b)             = Bool-show b
  show (integer i)          = Integer.show i
  show (quoted x)           = "'" ++ show x
  show (string x)           = "\"" ++ x ++ "\""
  show (list lst) =
    "(" ++ (foldr (λ hd acc → hd ++ " " ++ acc) id (map show lst)) ++ ")"

-- ----------------- ERRORS

-- Any error whatsoever
data Error : Set where
  err-ap         : String → Error
  err-parse      : String → Error
  err-noargs     : String → Error -- function applied to no arguments
  err-undefined  : String → Error
  err-type       : String → String → Error  -- expected, actual

-- ----------------- CASTS

-- Casts from Lisp to a specific type

module Cast where

  constructor-name : LispM.Lisp → String
  constructor-name (LispM.atom x)    = "atom"
  constructor-name (LispM.bool x)    = "bool"
  constructor-name (LispM.integer x) = "integer"
  constructor-name (LispM.string x)  = "string"
  constructor-name (LispM.quoted x)  = "quoted"
  constructor-name (LispM.list x)    = "list"

  integer : LispM.Lisp → Error ⊎ ℤ
  integer (LispM.integer x) = inj₂ x
  integer x                = inj₁ (err-type "integer" (constructor-name x))

  bool : LispM.Lisp → Error ⊎ Bool
  bool (LispM.bool x) = inj₂ x
  bool x             = inj₁ (err-type "bool" (constructor-name x))

open LispM public
