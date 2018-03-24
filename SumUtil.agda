module SumUtil where

open import Data.List              as List   using (List ; [] ; _∷_)
open import Data.Sum                 as Sum
open import Data.Product                     using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function                         using (_$_ ; _∘_ ; id)
open import Data.List.NonEmpty  as NonEmpty  renaming (map to map⁺ ; foldl to foldl⁺)
open import Level

-- Additional utilities for dealing with Sum types

-- TODO: https://github.com/agda/agda-stdlib/pull/221
_>>=_ : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
      → (A ⊎ B) → (B → A ⊎ C) → (A ⊎ C)
_>>=_  = λ x f → [ inj₁ , f ]′ x

_<$⊎>_ :  ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
       → (B → C) → A ⊎ B  → A ⊎ C
_<$⊎>_ = λ f → map id f

-- Like Haskell's partitionEither
partition : ∀ {a b : Level} {A : Set a} {B : Set b}
          → List (A ⊎ B) → List A × List B
partition = List.foldl (λ acc → [ (λ a → (a ∷ proj₁ acc , proj₂ acc)) ,
                                  (λ b → (proj₁ acc , b ∷ proj₂ acc)) ]′)
                       ([] , [])

-- Like Haskell's sequence, but relies on a pure computation and is less
-- efficient
sequenceᵣ : ∀ {a b : Level} {A : Set a} {B : Set b} → List (A ⊎ B) → A ⊎ (List B)
sequenceᵣ l = sequence-helper (partition l)
  where sequence-helper : ∀ {A B} → List A × List B → A ⊎ (List B)
        sequence-helper (a ∷ as , bs) = inj₁ a
        sequence-helper ([] , bs) = inj₂ bs

-- Unlike sequenceᵣ, this one is not strictly less general than partition.
-- We get a guarantee that the list of Bs is non-empty.
sequenceᵣ⁺ : ∀ {a b : Level} {A : Set a} {B : Set b} → List⁺ (A ⊎ B) → A ⊎ (List⁺ B)
sequenceᵣ⁺ = foldl⁺ [ (λ a _ → inj₁ a) , (λ lst x → (λ hd → hd ∷⁺ lst) <$⊎> x) ]′
                    (λ z → (λ x → [ x ]) <$⊎> z)
