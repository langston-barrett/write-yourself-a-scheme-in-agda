module test where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (suc n) + m = suc (n + m)

  data even : ℕ → Set where
    ZERO : even zero
    STEP : ∀ {x : ℕ} → even x → even (suc (suc x))

  proof₁ : even (suc (suc zero))
  proof₁ = STEP ZERO

  proof₂ : even (suc (suc (suc (suc zero))))
  proof₂ = STEP (STEP ZERO)

  id : {A : Set} → A → A
  id z = z

  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  ∧-elim-l : ∀ {P Q} → (P ∧ Q) → P
  ∧-elim-l (∧-intro p q) = p

  ∧-elim-r : ∀ {P Q} → (P ∧ Q) → Q
  ∧-elim-r (∧-intro p q) = q

  data _∨_ (P : Set) (Q : Set) : Set where
    ∨-intro-l : P → (P ∨ Q)
    ∨-intro-r : Q → (P ∨ Q)

  _⇔_ : (P : Set) → (Q : Set) → Set
  A ⇔ B = (A → B) ∧ (B → A)

  ∨-elim : ∀ {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q) → R
  ∨-elim f g (∨-intro-l p) = f p
  ∨-elim f g (∨-intro-r q) = g q

  ∧-comm : ∀ {P Q : Set} → (P ∧ Q) → (Q ∧ P)
  ∧-comm (∧-intro x y) = ∧-intro y x

  ∨-comm′ : ∀ {P Q : Set} → (P ∨ Q) → (Q ∨ P)
  ∨-comm′ (∨-intro-l x) = ∨-intro-r x
  ∨-comm′ (∨-intro-r x) = ∨-intro-l x

  ∨-comm : ∀ {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
  ∨-comm = ∧-intro ∨-comm′ ∨-comm′

  -- Brutal meta-introduction
  module ThrowAway where
    data Bool : Set where
      true false : Bool

    data Id (A : Set) : Set where
      pack : A → Id A

    data ⊥ : Set where

    not : Bool → Bool
    not true = false
    not false = true

    tt : {A : Set} → A → Bool
    tt _ = x
      where x = true

    record Person : Set where
      field
        big : Bool
        age : ℕ

