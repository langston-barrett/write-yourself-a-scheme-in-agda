module Error where

open import Function                            using    (id ; _∘_)
open import Data.String              as String  using    (String ; _++_)
open import Data.Sum                 as Sum     using    (_⊎_ ; inj₁ ; inj₂ )

-- ----------------- ERRORS

-- The generic constructor "err" is used to make "Error ⊎"
-- into a MonadPlus, it is the "zero" value.
data Error : Set where
  err-parse      : String → Error
  err-noargs     : String → Error -- function applied to no arguments
  err-undefined  : String → Error
  err-type       : String → String → Error  -- expected, actual

show-error : Error → String
show-error (err-parse str)    = "[ERR] No parse: " ++ str
show-error (err-noargs fun)   = "[ERR] Function called with no args: " ++ fun
show-error (err-undefined u)  = "[ERR] Undefined: " ++ u
show-error (err-type exp act) = "[ERR]: Expected " ++ exp ++ ", found " ++ act

errorOr : ∀ {a} (A : Set a) → (Set a)
errorOr t = Error ⊎ t
