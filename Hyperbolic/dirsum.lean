import Mathlib

variable {k V V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]
         
open LinearMap
open LinearMap (BilinForm)


def ProductBilinForm (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) : 
    BilinForm k (V₁ × V₂) :=
  let γ₁ : BilinForm k (V₁ × V₂) := 
    LinearMap.compl₁₂ 
      β₁
      (LinearMap.fst k V₁ _)
      (LinearMap.fst k V₁ _)
  let γ₂ : BilinForm k (V₁ × V₂) := 
    LinearMap.compl₁₂
      β₂
      (LinearMap.snd k _ V₂)
      (LinearMap.snd k _ V₂)
  γ₁ + γ₂ 

@[simp]
theorem product_bilin_form_apply (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂)
    (x y : V₁ × V₂) :
  ProductBilinForm β₁ β₂ x y = (β₁ x.fst y.fst) + (β₂ x.snd y.snd) := by
    aesop

theorem product_orthogonal (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂)
    (v₁ : V₁) (v₂ : V₂) :
  ProductBilinForm β₁ β₂ ⟨v₁,0⟩ ⟨0,v₂⟩ = 0 := by simp
  
def LinearMap.EpsilonSkew (β : BilinForm k V) (ε : k) : Prop :=
  ∀ x y, β x y = ε * β y x
  
theorem product_skew (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) (ε : k)
    (h₁ : β₁.EpsilonSkew ε) (h₂ : β₂.EpsilonSkew ε) :
  (ProductBilinForm β₁ β₂).EpsilonSkew ε := by
  intro x y
  simp only [product_bilin_form_apply]
  rw [ h₁, h₂]
  ring




