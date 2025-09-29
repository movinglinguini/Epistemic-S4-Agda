{- 
  Rules for type relations. 
  We take after Zdancewic, Grossman, and Morrisset (1999) Principals in programming languages, and 
  adapt their type-mapping rules to our setting.
-}
module EpistemicS4.TypeMappingRules 
  (PropAtom : Set) 
  (Agent : Set) 
  (decEqAgent : (a b : Agent) → Dec (a ≡ b))
  where

  open import EpistemicS4.Core.Propositions Agent PropAtom

  infix 50 _∼_