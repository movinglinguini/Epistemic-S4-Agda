{-
  EpistemicS4.agda

  An implementation of the Epistemic S4 modal logic natural deduction system in Agda.
-}
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

module EpistemicS4.NaturalDeduction 
  (Agent : Set) 
  (PropAtom : Set) 
  (decEqAgent : (a b : Agent) → Dec (a ≡ b))
  where

  open import EpistemicS4.Core.Terms Agent public
  open import EpistemicS4.Core.Propositions Agent PropAtom public

    
