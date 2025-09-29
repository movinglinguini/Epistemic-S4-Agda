{- Terms for the epistemic S4 lambda calculus -}
module EpistemicS4.Core.Terms (Agent : Set) where
  open import Data.String

  data Term : Set where
    {- Variables -}
    var : String → Term
    {- Abstraction/application -}
    ƛ_⇒_ : String → Term → Term
    _∙_ : Term → Term → Term
    {- Box/let-box -}
    box : Agent → Term → Term
    letbox_∣_≐_⇒_ : Agent → String → Term → Term → Term