module SumUtil where

open import Category.Functor
open import Category.Monad
open import Data.List           as List      using (List ; [] ; _∷_)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺)
                                             hiding (lift)
open import Data.Product                     using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum            as Sum
open import Function                         using (_$_ ; _∘_ ; id)
open import Level

-- Additional utilities for dealing with Sum types

open import Error

-- TODO: https://github.com/agda/agda-stdlib/pull/221
functorₗ : ∀ {a} (A : Set a) → (b : Level)
        → RawFunctor {a ⊔ b} (λ (B : Set (a ⊔ b)) → A ⊎ B)
functorₗ A b = record { _<$>_ = λ f → map id f }

-- The monad instance also requires some mucking about with universe levels.
monadₗ : ∀ {a} (A : Set a) → (b : Level)
      → RawMonad {a ⊔ b} (λ (B : Set (a ⊔ b)) → A ⊎ B)
monadₗ A b = record
  { return = λ x → inj₂ x
  ; _>>=_  = λ x f → [ inj₁ , f ]′ x
  }

-- Like Haskell's partitionEither
partition : ∀ {a b : Level} {A : Set a} {B : Set b}
          → List (A ⊎ B) → List A × List B
partition = List.foldl (λ acc → [ (λ a → (a ∷ proj₁ acc , proj₂ acc)) ,
                                  (λ b → (proj₁ acc , b ∷ proj₂ acc)) ]′)
                       ([] , [])

-- Like Haskell's sequence, but relies on a pure computation and is less
-- efficient
sequenceᵣ : ∀ {a b : Level} {A : Set a} {B : Set b} → List (A ⊎ B) → A ⊎ (List B)
sequenceᵣ = sequence-helper ∘ partition
  where sequence-helper : ∀ {A B} → List A × List B → A ⊎ (List B)
        sequence-helper (a ∷ as , bs) = inj₁ a
        sequence-helper ([] , bs) = inj₂ bs

-- Unlike sequenceᵣ, this one is not strictly less general than partition.
-- We get a guarantee that the list of Bs is non-empty.
-- enhancement: This could probably be more universe-polymorphic.
sequenceᵣ⁺ : ∀ {A B : Set} → List⁺ (A ⊎ B) → A ⊎ (List⁺ B)
sequenceᵣ⁺ {A} = foldl⁺ [ (λ a _ → inj₁ a) , (λ lst x → (λ hd → hd ∷⁺ lst) <$> x) ]′
                        (λ z → (λ x → [ x ]) <$> z)
  where open RawFunctor {Level.zero} (functorₗ A Level.zero)
