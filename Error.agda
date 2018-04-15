module Error where

open import Function                            using    (id ; _∘_)
open import Data.String              as String  using    (String ; _++_)
open import Data.Sum                 as Sum     using    (_⊎_ ; inj₁ ; inj₂ )
open import Data.Nat                            using    (ℕ)
open import Data.Nat.Show                       using    (show)

-- ----------------- ERRORS

-- The generic constructor "err" is used to make "Error ⊎"
-- into a MonadPlus, it is the "zero" value.
data Error : Set where
  err-parse      : String → Error
  err-undefined  : String → Error
  err-type       : String → String → Error  -- expected, actual
  err-arity₀     : String → Error           -- actual, name
  err-arity      : ℕ → ℕ → String → Error  -- expected, actual, name

show-error : Error → String
show-error (err-parse str)    = "[ERR] No parse: " ++ str
show-error (err-undefined u)  = "[ERR] Undefined: " ++ u
show-error (err-type exp act) = "[ERR]: Expected " ++ exp ++ ", found " ++ act
show-error (err-arity₀ f)  =
  "[ERR] Function " ++ f ++ " called with no arguments when some were expected."
show-error (err-arity x y f)  =
  "[ERR] Function " ++ f ++ " called with " ++
  show y ++ " arguments when " ++ show x ++ " were expected."

errorOr : ∀ {a} (A : Set a) → (Set a)
errorOr t = Error ⊎ t

throw : ∀ {a} {A : Set a} → Error → errorOr A
throw = inj₁
