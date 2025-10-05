module Invertibility.Loopspace where

open import Invertibility.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding

open import Cubical.Homotopy.Loopspace

open import Cubical.Data.Nat
open import Cubical.Data.Sigma       

ΩfunExtFamIso : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Pointed ℓ') →
  Iso (typ (Ω (Πᵘ∙ A B))) ((x : A) → typ (Ω (B x)))
ΩfunExtFamIso A B .Iso.fun p x i = p i x
ΩfunExtFamIso A B .Iso.inv p i x = p x i
ΩfunExtFamIso A B .Iso.rightInv p i x = p x
ΩfunExtFamIso A B .Iso.leftInv p i x = p x

ΩfunExtFam∙ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Pointed ℓ') →
  (Ω (Πᵘ∙ A B)) ≃∙ Πᵘ∙ A (λ x → Ω (B x))
ΩfunExtFam∙ A B = (isoToEquiv (ΩfunExtFamIso A B)) , refl

hasInverseIdfun : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
                → ((hasInverse (suc n)) (idfun A)) ≃ (∀ (x y : A) → (hasInverse n) (idfun (x ≡ y)))
hasInverseIdfun {A = A} n =
  compEquiv
    (invEquiv Σ-assoc-≃)
    (Σ-contractFst quasiAdjointSingleton)

hasInverseΩ : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
            → ((hasInverse n) (idfun A)) ≃ (∀ (x : A) → typ ((Ω^ n) (A , x)))
hasInverseΩ {A = A} zero = idEquiv (A → A)
hasInverseΩ {A = A} (suc n) =
  (hasInverse (suc n)) (idfun A)                         ≃⟨ hasInverseIdfun n ⟩
  (∀ (x y : A) → (hasInverse n) (idfun (x ≡ y)))         ≃⟨ equivΠCod (λ x → equivΠCod (λ y → hasInverseΩ n)) ⟩
  (∀ (x y : A) (p : x ≡ y) → typ ((Ω^ n) ((x ≡ y) , p))) ≃⟨ equivΠCod (λ x → invEquiv curryEquiv) ⟩
  (∀ (x : A) (ϕ : Σ[ y ∈ A ] x ≡ y) → typ ((Ω^ n) ((x ≡ fst ϕ) , snd ϕ))) ≃⟨ equivΠCod (λ x → Π-contractDom (isContrSingl x)) ⟩
  (∀ (x : A) → typ ((Ω^ n) ((x ≡ x) , refl)))            ≃⟨ equivΠCod (λ x → isoToEquiv (invIso (flipΩIso n))) ⟩
  (∀ (x : A) → typ ((Ω^ (suc n)) (A , x))) ■

ΩUniv : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
      → (Ω^ (suc (suc n))) (Type ℓ , A) ≃∙ (Πᵘ∙ A (λ x → (Ω^ (suc n)) (A , x)))
ΩUniv zero .fst =
  _ ≃⟨ congEquiv univalence ⟩
  _ ≃⟨ pathToEquiv (cong₂ _≡_ pathToEquivRefl pathToEquivRefl)  ⟩ 
  _ ≃⟨ cong fst , isEmbeddingFstΣProp (λ f → isPropIsEquiv f) ⟩
  _ ≃⟨ invEquiv funExtEquiv ⟩
  _ ■
ΩUniv zero .snd =
  funExt⁻ (cong fst (transport (cong₂ _≡_ pathToEquivRefl pathToEquivRefl) refl))
    ≡⟨ cong funExt⁻ (cong (cong fst ) (substInPaths (λ z → z) (λ z → z) pathToEquivRefl refl)) ⟩
  funExt⁻ (cong fst ((sym pathToEquivRefl) ∙ refl ∙ pathToEquivRefl))
    ≡⟨ cong funExt⁻ (cong (cong fst) (cong (sym pathToEquivRefl ∙_) (sym (lUnit pathToEquivRefl)))) ⟩
  funExt⁻ (cong fst ((sym pathToEquivRefl) ∙ pathToEquivRefl))
    ≡⟨ cong funExt⁻ (cong (cong fst) (lCancel pathToEquivRefl)) ⟩
  (λ x → refl)
    ∎
ΩUniv {A = A} (suc n) = compEquiv∙
  (Ω≃∙ (ΩUniv n))
  (ΩfunExtFam∙ A (λ x → (Ω^ suc n) (A , x)))

hasInverseΩUniv : ∀ {ℓ} (A : Type ℓ) (n : ℕ)
                → ((hasInverse (suc n)) (idfun A)) ≃ typ ((Ω^ (suc (suc n))) ((Type ℓ) , A))
hasInverseΩUniv A n = compEquiv (hasInverseΩ (suc n)) (invEquiv (fst (ΩUniv n)))

-- hasInverseΩRefl : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (p : (hasInverse (suc (suc n))) (idfun A))
--                 → equivFun (hasInverseΩ (suc n)) (dropInverse (suc n) p) ≡ λ x → refl
-- hasInverseΩRefl {A = A} zero (g , r , H) = {!!}
-- hasInverseΩRefl {A = A} (suc n) (g , r , H) =
--   σ (α (λ x y → ϕ (suc n) (β (suc n) (dropInverse (suc (suc n)) (g , r , H)) x y)))       ≡⟨⟩
--   σ (α (λ x y → ϕ (suc n) (β (suc n) (g , r , λ z w → dropInverse (suc n) (H z w)) x y))) ≡⟨⟩
--   σ (α (λ x y → ϕ (suc n) (subst
--     (λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))
--     (sym (quasiAdjointContraction (g , r)))
--     (λ z w → dropInverse (suc n) (H z w)) x y)))
--       ≡⟨ congS (σ ∘ α) (funExt₂ (λ x y → lemma x y (g , r) (quasiAdjointContraction (g , r)) H)) ⟩
--   σ (α (λ x y p → refl)) ≡⟨⟩
--   σ (λ x → refl) ≡⟨ funExt (λ x → cong (Iso.inv (flipΩIso (suc n))) (sym (flipΩrefl n)) ∙
--                            Iso.leftInv (flipΩIso (suc n)) refl) ⟩
--   (λ x → refl) ∎
--   where

--   σ : (∀ (x : A) → typ ((Ω^ (suc n)) ((x ≡ x) , refl))) → (∀ (x : A) → typ ((Ω^ (suc (suc n))) (A , x)))
--   σ p x = (Iso.inv (flipΩIso (suc n))) (p x)

--   α : (∀ (x y : A) (p : x ≡ y) → typ ((Ω^ (suc n)) ((x ≡ y) , p))) → (∀ (x : A) → typ ((Ω^ (suc n)) ((x ≡ x) , refl)))
--   α f x = f x x refl

--   ϕ : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
--     → ((hasInverse n) (idfun A)) → (∀ (x : A) → typ ((Ω^ n) (A , x)))
--   ϕ n = equivFun (hasInverseΩ n)

--   β : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
--     → ((hasInverse (suc n)) (idfun A)) → ∀ (x y : A) → (hasInverse n) (idfun (x ≡ y))
--   β n = equivFun (hasInverseIdfun n)

--   lemma : ∀ (x y : A) → (G : Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)
--         → (p : (idfun A , λ x y → idfun (x ≡ y)) ≡ G)
--         → (H : ∀ (x y : A) → (hasInverse (suc (suc n))) (snd G x y))
--         → ϕ (suc n) (subst
--             (λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))
--             (sym p)
--             (λ z w → dropInverse (suc n) (H z w)) x y) ≡
--           λ _ → refl
--   lemma x y G =
--     J
--       (λ G p → (H : ∀ (x y : A) → (hasInverse (suc (suc n))) (snd G x y)) →
--       ϕ (suc n) (subst
--         (λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))
--         (sym p)
--         (λ z w → dropInverse (suc n) (H z w)) x y) ≡
--       λ _ → refl)
--       {!!} where


--       lemma2 : (H : ∀ (x y : A) → (hasInverse (suc (suc n))) (idfun (x ≡ y)))
--              → (∀ (x y : A) → ϕ (suc n) (dropInverse (suc n) (H x y)) ≡ λ _ → refl)
--              → ϕ (suc n) (subst {A = (Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)}
--                  (λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))
--                  refl
--                  (λ z w → dropInverse (suc n) (H z w)) x y) ≡
--                λ _ → refl
--       lemma2 H p =
--         congS
--           {x = (subst
--             {A = (Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)}
--             λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))
--             refl
--             (λ z w → dropInverse (suc n) (H z w)) x y}
--           (ϕ (suc n))
--           (λ i → substRefl
--             {A = (Σ[ g ∈ (A → A) ] quasiAdjoint (idfun A) g)}
--             {B = (λ a → (x y : A) → (hasInverse (suc n)) (a .snd x y))}
--             ((λ z w → dropInverse (suc n) (H z w))) i x y) ∙ (p x y)

  
