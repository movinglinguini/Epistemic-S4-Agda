module EpistemicS4.Core.Propositions 
  (Agent : Set) 
  (PropAtom : Set) 
  (ExtProp : Set)
  where

  -- These are the propositions in epistemic S4.
  data Proposition : Set where
    {- Atomic propositions -}
    atom : PropAtom → Proposition
    {- Logical connectives -}
    -- Implication
    _⊃_ : Proposition → Proposition → Proposition
    {- The epistemic modal operator -}
    ⟦_⟧ : Agent → Proposition → Proposition
    {- 
      An embedded proposition. That is a proposition from outside of our
      language of propositions.
     -}
    ⟪_⟫⟨_⟩ : ExtProp → Agent → Proposition
