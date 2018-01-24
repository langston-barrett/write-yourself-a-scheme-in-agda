module Util where

open import Data.List                as List    hiding ([_])
open import Data.Integer             as Integer using  (ℤ)
open import Data.Bool                as Bool    using  (Bool)
open import Data.String              as String  using (String)

-- ----------------- LANGUAGE

data Lisp : Set where
  atom        : String → Lisp
  list        : List Lisp → Lisp
  dotted-list : List Lisp → Lisp
  integer     : ℤ → Lisp
  string      : String → Lisp
  bool        : Bool → Lisp
