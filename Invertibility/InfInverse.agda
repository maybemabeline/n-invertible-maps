module Invertibility.InfInverse where

open import Invertibility.Base
open import Invertibility.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Loopspace

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit


record hasInverse∞ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    hasInverseN : ∀ (n : ℕ) → (hasInverse n) f
    coh : ∀ (n : ℕ) → dropInverse n (hasInverseN (suc n)) ≡ hasInverseN n
open hasInverse∞    

forgetCoh : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
          → hasInverse∞ f → (n : ℕ) → (hasInverse n) f
forgetCoh = hasInverse∞.hasInverseN

equivToHasInverse∞ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                   → (e : A ≃ B) → hasInverse∞ (equivFun e)
equivToHasInverse∞ e .hasInverse∞.hasInverseN = equivToHasInverseN e
equivToHasInverse∞ e .hasInverse∞.coh = equivToHasInverseNCoh e

hasInverseNIdContr : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr ((hasInverse n) (idfun A))
hasInverseNIdContr zero c = isContrΠ (λ x → c)
hasInverseNIdContr (suc n) c =
  subst
    isContr
    (ua Σ-assoc-≃)
    (isContrΣ'
      quasiAdjointSingleton
      (isContrΠ (λ x → isContrΠ (λ y → hasInverseNIdContr n (isContr→isContrPath c x y)))))

hasInverse∞IdContr : ∀ {ℓ} {A : Type ℓ} → isContr A → isContr (hasInverse∞ (idfun A))
hasInverse∞IdContr c =
  isContrRetract
    forgetCoh
    (λ α → record {
      hasInverseN = α ;
      coh = λ n → fst (isContr→isContrPath (hasInverseNIdContr n c) _ _)
      }
    )
    (λ α i → record {
      hasInverseN = forgetCoh α ;  
      coh = λ n → snd (isContr→isContrPath (hasInverseNIdContr n c) _ _) (α .hasInverse∞.coh n) i
      }
    )
    (isContrΠ (λ n → hasInverseNIdContr n c))


-- Unfolding the type of ∞-inverses is an equivalence

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (e : hasInverse∞ f) where

  g : ∀ (n : ℕ) → B → A
  g n = invN (e .hasInverseN (suc n))

  r : ∀ (n : ℕ) → quasiAdjoint f (g n)
  r n = qAdjN (e .hasInverseN (suc n))

  H : ∀ (n : ℕ) (x : A) (y : B) → (hasInverse n) (r n x y)
  H n = snd (snd (e .hasInverseN (suc n)))

  assocCoh : ∀ (n : ℕ) → (_,_ {B = λ h → quasiAdjoint f h} (g (suc n)) (r (suc n))) ≡ (g n , r n)
  assocCoh n i = (fst (e .coh (suc n) i)) , fst (snd (e .coh (suc n) i))

  assocCohFull : ∀ (n : ℕ) → (_,_ {B = λ h → quasiAdjoint f h} (g n) (r n)) ≡ (g 0 , r 0)
  assocCohFull zero = refl
  assocCohFull (suc n) = assocCoh n ∙ assocCohFull n

  improveCoh : ∀ (n : ℕ) (x : A) (y : B) → (hasInverse n) (r 0 x y)
  improveCoh n =
     subst
       {A = Σ[ h ∈ (B → A) ] quasiAdjoint f h}
       (λ {(_ , s) → ∀ (x : A) (y : B) → (hasInverse n) (s x y)})
       (assocCohFull n)
       (H n)

  assocCohFull-filler : ∀ (n : ℕ) → PathP (λ i → ∀ (x : A) (y : B) → (hasInverse n) (snd (assocCohFull n i) x y)) (H n) (improveCoh n)
  assocCohFull-filler n = subst-filler (λ {(_ , s) → ∀ (x : A) (y : B) → (hasInverse n) (s x y)}) (assocCohFull n) (H n)

  β : ∀ (n : ℕ)
    → PathP (λ i → ∀ (x : A) (y : B) → (hasInverse n) (snd ((sym (assocCohFull (suc n)) ∙ assocCohFull (suc n)) i) x y))
            (λ x y → dropInverse n (improveCoh (suc n) x y))
            (improveCoh n)
  β n =
    compPathP'
      {B = λ {(_ , s) → ∀ (x : A) (y : B) → (hasInverse n) (s x y)}}
      {p = sym (assocCohFull (suc n))}
      {q = assocCohFull (suc n)}
      (funExt₂ (λ x y → congP (λ i → dropInverse n) (λ i → symP (assocCohFull-filler (suc n)) i x y)))
      (compPathP'
        {B = λ {(_ , s) → ∀ (x : A) (y : B) → (hasInverse n) (s x y)}}
        {p = assocCoh n}
        {q = assocCohFull n}
        (λ i → snd (snd (e .coh (suc n) i)))
        (assocCohFull-filler n))

  α : ∀ (n : ℕ) → (λ x y → dropInverse n (improveCoh (suc n) x y)) ≡ (improveCoh n)
  α n = subst
    (λ p → PathP
      (λ i → ∀ (x : A) (y : B) → (hasInverse n) (snd (p i) x y))
      (λ x y → dropInverse n (improveCoh (suc n) x y))
      (improveCoh n))
    (lCancel (assocCohFull (suc n)))
    (β n)


unfoldHasInverse∞ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} → hasInverse∞ f
                   → Σ[ g ∈ (B → A) ] Σ[ r ∈ (quasiAdjoint f g) ] (∀ (x : A) (y : B) → hasInverse∞ (r x y))
unfoldHasInverse∞ e .fst = g e 0
unfoldHasInverse∞ e .snd .fst = r e 0
unfoldHasInverse∞ e .snd .snd x y = record {
  hasInverseN = λ n → improveCoh e n x y ;
  coh = λ n i → α e n i x y
  }

foldHasInverse∞ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
                → Σ[ g ∈ (B → A) ] Σ[ r ∈ (quasiAdjoint f g) ] (∀ (x : A) (y : B) → hasInverse∞ (r x y))
                → hasInverse∞ f
foldHasInverse∞ (g , r , H) = record {
  hasInverseN = λ { zero → g ; (suc n) → (g , r , λ x y → H x y .hasInverse∞.hasInverseN n)} ;
  coh = λ { zero → refl ; (suc n) → λ i → (g , r , (λ x y → H x y .hasInverse∞.coh n i))}
  }

foldUnfoldHasInverse∞ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
                      → (α : hasInverse∞ f)
                      → (foldHasInverse∞ (unfoldHasInverse∞ α) ≡ α)
foldUnfoldHasInverse∞ record { hasInverseN = e ; coh = coh } i = record {
  hasInverseN = λ n → {!!} ;
  coh = {!!}
  } where

unfoldFoldHasInverse∞ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
                      → (α : Σ[ g ∈ (B → A) ] Σ[ r ∈ (quasiAdjoint f g) ] (∀ (x : A) (y : B) → hasInverse∞ (r x y)))
                      → (unfoldHasInverse∞ (foldHasInverse∞ α) ≡ α)
unfoldFoldHasInverse∞ {A = A} {B = B} {f = f} (g , r , H) = {!!} where

  assocCohFullrefl : ∀ (n : ℕ) → assocCohFull (foldHasInverse∞ (g , r , H)) n ≡ refl
  assocCohFullrefl zero = refl
  assocCohFullrefl (suc n) = sym (lUnit (assocCohFull (foldHasInverse∞ (g , r , H)) n )) ∙ assocCohFullrefl n

  improveCohrefl : ∀ (n : ℕ) → improveCoh (foldHasInverse∞ (g , r , H)) n ≡ λ x y → H x y .hasInverseN n
  improveCohrefl n = {!!}

mjau : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
     → Iso
         (hasInverse∞ f)
         (Σ[ g ∈ (B → A) ] Σ[ r ∈ (quasiAdjoint f g) ] (∀ (x : A) (y : B) → hasInverse∞ (r x y)))
mjau .Iso.fun = unfoldHasInverse∞
mjau .Iso.inv = foldHasInverse∞
mjau .Iso.rightInv = unfoldFoldHasInverse∞
mjau .Iso.leftInv = foldUnfoldHasInverse∞
     
