module Language where

open import Category.Monad
open import Function                            using    (id ; _∘_ ; _$_)
open import Data.List                           hiding   (_++_)
open import Data.List.NonEmpty                  renaming (map to map⁺; foldr to foldr⁺)
open import Data.Integer             as Integer using    (ℤ)
open import Data.Bool                as Bool    hiding   (_≟_)
open import Data.Bool.Show                      renaming (show to Bool-show)
open import Data.String              as String  using    (String ; _++_)
open import Data.Sum                 as Sum     using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Product             as Product using (proj₁ ; proj₂ ; _,_ ; _×_)
open import Relation.Nullary.Decidable          using (⌊_⌋)
open import Level
open import Size

open import Error
open import SumUtil

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
    -- enhancement: this should be made into vectors of length > 1
    list        : ∀ {j : Size< i} → List (Lisp {j}) → Lisp

  -- ----------------- SHOW

  show : ∀ {i} → Lisp {i} → String
  show (atom s)             = s
  show (bool b)             = Bool-show b
  show (integer i)          = Integer.show i
  show (quoted x)           = "'" ++ show x
  show (string x)           = "\"" ++ x ++ "\""
  show (list [])            = "()"
  show (list (x ∷ []))      = "(" ++ show x ++ ")"
  show (list (x ∷ xs))      =
    "(" ++ show x ++ (foldr (λ hd acc → " " ++ hd ++ acc) "" (map show xs)) ++ ")"

  -- ----------------- EQUALITY

  -- TODO: make this a proper decidable relation as in stdlib
  _≟_ : ∀ {i} → Lisp {i} → Lisp {i} → Bool
  _≟_ (atom    x) (atom    y) = ⌊ String._≟_  x y ⌋
  _≟_ (bool    x) (bool    y) = ⌊ Bool._≟_    x y ⌋
  _≟_ (integer x) (integer y) = ⌊ Integer._≟_ x y ⌋
  _≟_ (string  x) (string  y) = ⌊ String._≟_  x y ⌋
  _≟_ (quoted  x) (quoted  y) = x ≟ y
  -- ---------- Lists
  _≟_ (list (hd₁ ∷ []))         (list    (hd₂ ∷ []))  = hd₁ ≟ hd₂
  _≟_ (list (hd₁ ∷ (hd₂ ∷ tl₁))) (list    (hd₃ ∷ tl₂)) = false -- TODO
  -- hd₁ ≟ hd₂ ∧ (Lisp.list (hd₂ ∷ tl₁) ≟ Lisp.list (hd₃ ∷ tl₂))
  _≟_ _ _ = false -- all other combinations don't make sense

-- ----------------- CASTS

-- Casts from Lisp to a specific type

cast : ∀ {a} → Set a → Set a
cast T = LispM.Lisp → errorOr T

castM : ∀ {a} → (M : Set → Set a) → Set → Set a
castM M T = M LispM.Lisp → errorOr (M T)

module Cast where

  open RawMonad (monadₗ Error zero)

  constructor-name : LispM.Lisp → String
  constructor-name (LispM.atom x)    = "atom"
  constructor-name (LispM.bool x)    = "bool"
  constructor-name (LispM.integer x) = "integer"
  constructor-name (LispM.string x)  = "string"
  constructor-name (LispM.quoted x)  = "quoted"
  constructor-name (LispM.list x)    = "list"

  integer : cast ℤ
  integer (LispM.integer x) = return x
  integer x                 = throw $ err-type "integer" (constructor-name x)
    where

  bool : cast Bool
  bool (LispM.bool x) = return x
  bool x              = throw $ (err-type "bool" (constructor-name x))

  quoted-list⁺ : cast (List⁺ LispM.Lisp)
  quoted-list⁺ (LispM.quoted (LispM.list (x ∷ xs))) = return (x ∷ xs)
  quoted-list⁺ (LispM.quoted (LispM.list [])) =
    throw $ err-type "nonempty list" "empty list"
  quoted-list⁺ (LispM.quoted _) = throw $ err-type "quoted list" "quoted non-list"
  quoted-list⁺ _ = throw $ err-type "quoted list" "non-quoted term"

  list : ∀ {A : Set} → cast A → castM List A
  list c = sequenceᵣ ∘ (map c)

  list⁺ : ∀ {A : Set} → cast A → castM List⁺ A
  list⁺ c = sequenceᵣ⁺ ∘ (map⁺ c)

  integers : castM List ℤ
  integers = list integer

  -- integers⁺ : castM List ℤ
  -- integers⁺ = list⁺ integer

open LispM public
