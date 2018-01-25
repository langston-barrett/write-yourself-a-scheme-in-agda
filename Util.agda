module Util where

open import Data.List.NonEmpty                  using (List⁺ ; toList)
open import Data.Integer             as Integer using  (ℤ)
open import Data.Bool                as Bool    using  (Bool)
open import Data.String              as String  using (String)

-- ----------------- LANGUAGE

data Lisp : Set where
  atom        : String → Lisp
  bool        : Bool → Lisp
  dotted-list : List⁺ Lisp → Lisp
  integer     : ℤ → Lisp
  list        : List⁺ Lisp → Lisp
  quoted      : Lisp → Lisp
  string      : String → Lisp
