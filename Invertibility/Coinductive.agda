{-# OPTIONS --guardedness #-}
module Invertibility.Coinductive where

open import Invertibility.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

record is-∞-equiv
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ')
  where
  coinductive
  field
    map : B → A
    transpose :
      (x : A) (y : B) → f x ≡ y → x ≡ map y
    transpose-equiv :
      (x : A) (y : B) → is-∞-equiv (transpose x y)

open is-∞-equiv public

unfold∞Equiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
             → Iso (Σ[ g ∈ (B → A) ] Σ[ r ∈ ((x : A) (y : B) → f x ≡ y → x ≡ g y)] (∀ (x : A) (y : B) → is-∞-equiv (r x y))) (is-∞-equiv f)
unfold∞Equiv f .Iso.fun (g , r , ϕ) .map = g
unfold∞Equiv f .Iso.fun (g , r , ϕ) .transpose = r
unfold∞Equiv f .Iso.fun (g , r , ϕ) .transpose-equiv = ϕ
unfold∞Equiv f .Iso.inv e .fst = e .map
unfold∞Equiv f .Iso.inv e .snd .fst = e .transpose
unfold∞Equiv f .Iso.inv e .snd .snd = e .transpose-equiv
unfold∞Equiv f .Iso.rightInv e i .map = e .map
unfold∞Equiv f .Iso.rightInv e i .transpose = e .transpose
unfold∞Equiv f .Iso.rightInv e i .transpose-equiv = e .transpose-equiv
unfold∞Equiv f .Iso.leftInv u = refl

characterise∞EquivIdfun : ∀ {ℓ} (A : Type ℓ)
                        → (∀ (x y : A) → is-∞-equiv (idfun (x ≡ y))) ≃ (is-∞-equiv (idfun A))
characterise∞EquivIdfun A =
  compEquiv
    (compEquiv
      (invEquiv (Σ-contractFst quasiAdjointSingleton))
      Σ-assoc-≃)
    (isoToEquiv (unfold∞Equiv (idfun A)))

isContr∞EquivIdfun : ∀ {ℓ} (A : Type ℓ) → isContr (is-∞-equiv (idfun A))
isContr∞EquivIdfun A =
  isOfHLevelRespectEquiv
    0
    (characterise∞EquivIdfun A)
    (isContrΠ (λ x → isContrΠ (λ y → isContr∞EquivIdfun (x ≡ y))))
