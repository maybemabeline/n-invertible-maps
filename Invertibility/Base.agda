module Invertibility.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Prod


-- Mystery missing function

Π-dom-swap : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
           → ((x : A) → (y : B) → C x y) ≃ ((y : B) → (x : A) → C x y)
Π-dom-swap = isoToEquiv (iso
  (λ f x y → f y x)
  (λ g y x → g x y)
  (λ _ → refl)
  (λ _ → refl))


-- Quasi adjoints - definition and properties

quasiAdjoint : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → (B → A) → Type (ℓ-max ℓ ℓ')
quasiAdjoint {A = A} {B = B} f g = (x : A) → (y : B) → f x ≡ y → x ≡ g y

quasiAdjointSection : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → (g : B → A)
                       → (quasiAdjoint f g) ≃ (∀ (x : A) → g (f x) ≡ x)
quasiAdjointSection {A = A} {B = B} f g =
  equivΠCod (λ x →
    (invEquiv curryEquiv) ∙ₑ
    (Π-contractDom (isContrSingl (f x))) ∙ₑ
    (isoToEquiv symIso))

quasiAdjointContraction : ∀ {ℓ} {A : Type ℓ} → (α : Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)
                        → (idfun A , λ x y → idfun (x ≡ y)) ≡ α
quasiAdjointContraction (g , r) i .fst x = r x x refl i
quasiAdjointContraction (g , r) i .snd x y p = J
  (λ z q → Square q (r x z q) refl (r z z refl))
  (λ i j → r x x refl (i ∧ j))
  p
  i
  
quasiAdjointSingleton : ∀ {ℓ} {A : Type ℓ} 
                      → isContr (Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)
quasiAdjointSingleton {A = A} =
  (idfun A , λ x y → idfun (x ≡ y)) ,
  (quasiAdjointContraction)


-- Definition of n-invertibility
  
hasInverse_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → ℕ → (A → B) → Type (ℓ-max ℓ ℓ')
hasInverse_ {A = A} {B = B} zero f = B → A
hasInverse_ {A = A} {B = B} (suc n) f =
  Σ[ g ∈ (B → A) ] Σ[ r ∈ (quasiAdjoint f g) ] ∀ (x : A) (y : B) → ((hasInverse n) (r x y))

invN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n : ℕ}
     → (hasInverse n) f → B → A
invN {n = zero} e = e
invN {n = suc n} e = fst e

qAdjN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n : ℕ}
      → (e : (hasInverse (suc n)) f) → quasiAdjoint f (invN e)
qAdjN {n = n} e = fst (snd e)

cohN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n : ℕ}
     → (e : (hasInverse (suc n)) f) → (x : A) (y : B) → (hasInverse n) ((qAdjN e) x y)
cohN e = snd (snd e)

-- Basic properties of n-invertibility

dropInverse : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → {f : A → B} → (n : ℕ)
            → (hasInverse (suc n)) f → (hasInverse n) f
dropInverse zero = fst
dropInverse (suc n) (g , r , H) = g , r , λ x y → dropInverse n (H x y)

idHasInverseN : ∀ {ℓ} {A : Type ℓ} → (n : ℕ) → (hasInverse n) (idfun A)
idHasInverseN zero x = x
idHasInverseN (suc n) .fst x = x
idHasInverseN (suc n) .snd .fst x y p = p
idHasInverseN (suc n) .snd .snd x y = idHasInverseN n


-- 1-invertibility is equivalent to being an isomorphism

hasInverse1IsIsoEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : A → B)
                      → (hasInverse 1) f ≃ isIso f
hasInverse1IsIsoEquiv f =
  Σ-cong-equiv-snd (λ g →
    compEquiv
      (≃-×
        (quasiAdjointSection f g)
        (equivΠCod (λ x → equivΠCod (λ y →
          compEquiv
            (preCompEquiv (isoToEquiv symIso))
            (postCompEquiv (isoToEquiv symIso)))) ∙ₑ
         Π-dom-swap ∙ₑ
         (quasiAdjointSection g f)))
      (Σ-swap-≃))


-- Passing between n-invertibility, isomorphism and equivalence

hasInverseNToIsIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → {f : A → B} → (n : ℕ)
                   → (hasInverse (suc n)) f → isIso f
hasInverseNToIsIso zero (g , ε , η) .fst = g
hasInverseNToIsIso zero (g , ε , η) .snd .fst y = η (g y) y refl
hasInverseNToIsIso {f = f} zero (g , ε , η) .snd .snd x = sym (ε x (f x) refl)
hasInverseNToIsIso (suc n) H = hasInverseNToIsIso n (dropInverse (suc n) H)


-- This construction can be viewed as a generalization of Vogt's lemma.
-- Given an isomorphism, it not only improves the second 2-cell so that it
-- is coherent with the first, it also improves the n-cell at every level.
isIsoToHasInverseN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} → (n : ℕ)
                   → isIso f → (hasInverse n) f
isIsoToHasInverseN zero = fst
isIsoToHasInverseN (suc n) (g , _ , _) .fst = g
isIsoToHasInverseN (suc n) (g , ε , η) .snd .fst x y q = sym (η x) ∙ cong g q
isIsoToHasInverseN {f = f} (suc n) e .snd .snd x y = isIsoToHasInverseN n (
  (λ p → cong f p ∙ ε y) ,
  (λ p → J
    (λ z p → sym (η z) ∙ cong g (cong f (sym p) ∙ ε y) ≡ (sym p))
    ( (cong (λ q → sym (η (g y)) ∙ cong g q) (sym (lUnit (ε y)))) ∙
      (cong (sym (η (g y)) ∙_) (K y) ∙
      (lCancel (η (g y)))))
    (sym p)) ,
  J (λ z q → cong f (sym (η x) ∙ cong g q) ∙ ε z ≡ q)
    ( (cong (λ p → cong f p ∙ ε (f x)) (sym (rUnit (sym (η x))))) ∙
      (cong (cong f (sym (η x)) ∙_) (sym (H x))) ∙
      (lCancel (cong f (η x))))) where

  e' : isHAEquiv f
  e' = snd (iso→HAEquiv (isIsoToIso e))

  g = isHAEquiv.g e'
  ε = isHAEquiv.rinv e'
  η = isHAEquiv.linv e'
  H = isHAEquiv.com e'
  K = isHAEquiv.com-op e'

equivToHasInverseN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} 
                     → (e : A ≃ B) → (n : ℕ) → (hasInverse n) (equivFun e)
equivToHasInverseN e zero = invEq e
equivToHasInverseN e (suc n) .fst = invEq e
equivToHasInverseN e (suc n) .snd .fst x y = equivFun (invEquiv (equivAdjointEquiv e))
equivToHasInverseN e (suc n) .snd .snd x y = equivToHasInverseN (invEquiv (equivAdjointEquiv e)) n

equivToHasInverseNCoh : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (e : A ≃ B) → (n : ℕ)
                        → dropInverse n (equivToHasInverseN e (suc n)) ≡ equivToHasInverseN e n
equivToHasInverseNCoh e zero = refl
equivToHasInverseNCoh e (suc n) = ΣPathP (refl , (ΣPathP (refl , (funExt λ x → funExt (λ y →
  equivToHasInverseNCoh (invEquiv (equivAdjointEquiv e)) n)))))
