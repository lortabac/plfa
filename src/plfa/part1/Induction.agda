module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

+-swap′ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap′ m n p
  rewrite sym (+-assoc m n p)
        | sym (+-assoc n m p)
        | +-comm m n
        = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-distrib-+′ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p
  rewrite cong (p +_) (*-distrib-+′ m n p)
        | +-assoc p (m * p) (n * p)
        = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + (m * (n * p))
  ≡⟨⟩
    suc m * (n * p)
  ∎

*-assoc′ : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc′ zero n p = refl
*-assoc′ (suc m) n p
  rewrite *-distrib-+ n (m * n) p
        | cong ((n * p) +_) (*-assoc′ m n p)
        = refl
