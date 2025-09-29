{-
  EpistemicS4.agda

  An implementation of the Epistemic S4 modal logic natural deduction system in Agda.
-}
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

module EpistemicS4 
  (Agent : Set) 
  (PropAtom : Set) 
  (decEqAgent : (a b : Agent) → Dec (a ≡ b))
  where
  
  open import Data.String
  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any
  open import Data.Product
  open import Relation.Nullary

  -- These are the propositions in epistemic S4.
  data Proposition : Set where
    {- Atomic propositions -}
    atom : PropAtom → Proposition
    {- Logical connectives -}
    -- Implication
    _⊃_ : Proposition → Proposition → Proposition
    {- The epistemic modal operator -}
    ⟦_⟧ : Agent → Proposition → Proposition

  
  postulate
    alice bob charlie : Agent
    exPropAtom1 exPropAtom2 : PropAtom

  private
    -- Some example propositions
    exampleProp1 : Proposition
    exampleProp1 = atom exPropAtom1 ⊃ ⟦ alice ⟧ (atom exPropAtom2)

    exampleProp2 : Proposition
    exampleProp2 = ⟦ bob ⟧ (atom exPropAtom1)

  {- Propositions are paired with qualifiers to form judgments -}
  infixr 100 _true
  infix 100 _knows_

  data Judgment : Set where
    {- A judgment can be a proposition known to be true -}
    _true : Proposition → Judgment
    {- A judgment can be a proposition known by an agent -}
    _knows_ : Agent → Proposition → Judgment

  private
    -- Some example judgments
    exampleJudgment1 : Judgment
    exampleJudgment1 = alice knows (atom exPropAtom1)

    exampleJudgment2 : Judgment
    exampleJudgment2 = (atom exPropAtom2) true

  {- Now we'll want to define terms that will be typed according with these propositons -}
  data Term : Set where
    {- Variables -}
    var : String → Term
    {- Implication -}
    ƛ_⇒_ : String → Term → Term
    _∙_ : Term → Term → Term
    {- Epistemic Modal Operator -}
    box : Agent → Term → Term
    let-box_∣_≐_⇒_ : Agent → String → Term → Term → Term

  -- Now, a pairing of terms and judgments to form typing statements.
  infix 50 _∶_
  data TypingStatement : Set where
    _∶_ : Term → Judgment → TypingStatement

  private 
    -- Example typing statements - These are not necessarily derivable.
    exampleTyping1 : TypingStatement
    exampleTyping1 = (var "x") ∶ (atom exPropAtom1) true

    exampleTyping2 : TypingStatement
    exampleTyping2 = (box alice (var "y")) ∶ ⟦ alice ⟧ (atom exPropAtom1) true

  -- Contexts in epistemic S4 are just lists of propositions.
  Context : Set
  Context = List TypingStatement

  -- Here, we work with two disjoint contexts: one for knowledge and one for truth.
  -- We want to differentiate between what is known by agents and what is simply true.
  data KnowsContext : Context → Set where
    knows-ctx/z : KnowsContext []
    knows-ctx/s : ∀ {Γ A a e} 
      → KnowsContext Γ 
      ------------------------------
      → KnowsContext (e ∶ (a knows A) ∷ Γ)
    
  data TrueContext : Context → Set where
    true-ctx/z : TrueContext []
    true-ctx/s : ∀ {Γ A e} 
      → TrueContext Γ 
      ------------------------------
      → TrueContext (e ∶ A true ∷ Γ)

  -- We'll also want to characterize contexts that have only the knowledge judgments
  -- of a specific agent. We define them in relation to a more general context.
  -- This will be useful for the knowledge introduction rule.
  data KnowsRestricted : Context → Agent → Context → Set where
    k-ctx/z : ∀ {a} → KnowsRestricted [] a []
    k-ctx/s-keep : ∀ {Γ Γ' A a e}
      → KnowsRestricted Γ a Γ'
      ------------------------------
      → KnowsRestricted (e ∶ (a knows A) ∷ Γ) a (e ∶ (a knows A) ∷ Γ')
    
    k-ctx/s-drop : ∀ {Γ Γ' A b a e}
      → KnowsRestricted Γ a Γ'
      → ¬ (a ≡ b)
      ------------------------------
      → KnowsRestricted (e ∶ (b knows A) ∷ Γ) a Γ'

  -- Generating knows-restricted contexts from a given context.
  restrictKnowsContext : ∀ {Γ a} → KnowsContext Γ → Σ (Context) (λ Γ|k → KnowsRestricted Γ a Γ|k)
  restrictKnowsContext knows-ctx/z = ([] , k-ctx/z)
  restrictKnowsContext {a = a} (knows-ctx/s {A = A} {a = b} {e = e} kΓ) with restrictKnowsContext { a = a } kΓ
  ... | (Γ|k , k-ctxt) with (decEqAgent a b)
  ... | yes refl = e ∶ a knows A ∷ Γ|k , k-ctx/s-keep k-ctxt
  ... | no ¬p = Γ|k , k-ctx/s-drop k-ctxt ¬p

  -- Some rules about knows-restriction.
  -- A knows-restricted context is always a knows context.
  Γ|k-is-knows : ∀ {Γ a Γ|k} → KnowsRestricted Γ a Γ|k → KnowsContext Γ|k
  Γ|k-is-knows k-ctx/z = knows-ctx/z
  Γ|k-is-knows (k-ctx/s-keep kΓ) = knows-ctx/s (Γ|k-is-knows kΓ)
  Γ|k-is-knows (k-ctx/s-drop kΓ ¬p) = Γ|k-is-knows kΓ

  -- A knows-restrict context restricted with the same agent is itself.
  Γ|k-knows-restrict-unit : ∀ {Γ a Γ|k} → KnowsRestricted Γ a Γ|k → KnowsRestricted Γ|k a Γ|k
  Γ|k-knows-restrict-unit k-ctx/z = k-ctx/z
  Γ|k-knows-restrict-unit (k-ctx/s-keep kΓ) = k-ctx/s-keep (Γ|k-knows-restrict-unit kΓ)
  Γ|k-knows-restrict-unit (k-ctx/s-drop kΓ ¬p) = Γ|k-knows-restrict-unit kΓ

  -- The natural deduction rules for epistemic S4.
  data _⊢_ : (Context × Context) → TypingStatement → Set where
    {- Hypothesis: If a proposition is in the true context, it can be derived -}
    hyp : ∀ {Γ Δ A x E}
      → KnowsContext Γ → TrueContext Δ
      → ((var x) ∶ A true) ∈ Δ
      -------------------------------
      → (Γ , Δ) ⊢ E ∶ A true

    {- 
      Hypothesis from knowledge: If we know something is true, then we can hypothesize
      it 
    -}
    hyp* : ∀ {Γ Δ A a x E}
      → KnowsContext Γ → TrueContext Δ
      → ((var x) ∶ (a knows A)) ∈ Γ
      -------------------------------
      → (Γ , Δ) ⊢ E ∶ A true

    {- Implication -}
    -- Implication Introduction
    ⊃I : ∀ {Γ Δ A B E x}
      → KnowsContext Γ → TrueContext Δ
      → (Γ , (var x) ∶ A true ∷ Δ) ⊢ E ∶ B true
      -------------------------------
      → (Γ , Δ) ⊢ (ƛ x ⇒ E) ∶ (A ⊃ B) true

    -- Implication Elimination
    ⊃E : ∀ {Γ Δ A B E1 E2}
      → KnowsContext Γ → TrueContext Δ
      → (Γ , Δ) ⊢ E1 ∶ (A ⊃ B) true
      → (Γ , Δ) ⊢ E2 ∶ A true
      -------------------------------
      → (Γ , Δ) ⊢ (E1 ∙ E2) ∶ B true
    
    {- Epistemic Modal Operator -}
    -- Knowledge Introduction
    ⟦⟧I : ∀ {Γ Γ|k Δ A a E}
      → KnowsContext Γ → TrueContext Δ → KnowsRestricted Γ a Γ|k
      → (Γ|k , []) ⊢ E ∶ A true
      -------------------------------
      → (Γ , Δ) ⊢ (box a E) ∶ ⟦ a ⟧ A true 

    -- Knowledge Elimination
    ⟦⟧E : ∀ {Γ Δ A C a E1 E2 x}
      → KnowsContext Γ → TrueContext Δ
      → (Γ , Δ) ⊢ E1 ∶ ⟦ a ⟧ A true → (((var x) ∶ (_knows_ a A)) ∷ Γ , Δ) ⊢ E2 ∶ C true
      -------------------------------
      → (Γ , Δ) ⊢ (let-box a ∣ x ≐ E1 ⇒ E2) ∶ C true 

  {- 
    Axiomatic characterization of epistemic S4.
  -}
  modusPonens : ∀ {A B E1 E2}
    → ([] , []) ⊢ E1 ∶ (A ⊃ B) true
    → ([] , []) ⊢ E2 ∶ A true
    -------------------------------
    → ([] , []) ⊢ (E1 ∙ E2) ∶ B true
  modusPonens mpAtoB mpA = ⊃E knows-ctx/z true-ctx/z mpAtoB mpA

  necessitation : ∀ {A a E}
    → ([] , []) ⊢ E ∶ A true
    -------------------------------
    → ([] , []) ⊢ (box a E) ∶ ⟦ a ⟧ A true
  necessitation D = ⟦⟧I knows-ctx/z true-ctx/z k-ctx/z D

  -- Distribution of knowledge over implication
  distribution : ∀ {A B a x y u w}
    → ([] , []) ⊢ (ƛ x ⇒ (ƛ y ⇒ (let-box a ∣ u ≐ (var x) ⇒ (let-box a ∣ w ≐ (var y) ⇒ box a ((var u) ∙ (var w)))))) ∶ ((⟦ a ⟧ (A ⊃ B)) ⊃ (⟦ a ⟧ A ⊃ ⟦ a ⟧ B)) true
  distribution = 
    ⊃I knows-ctx/z true-ctx/z 
      (⊃I knows-ctx/z (true-ctx/s true-ctx/z) 
        (⟦⟧E knows-ctx/z (true-ctx/s (true-ctx/s true-ctx/z)) 
          (hyp knows-ctx/z (true-ctx/s (true-ctx/s true-ctx/z)) (there (here refl))) 
          (⟦⟧E (knows-ctx/s knows-ctx/z) (true-ctx/s (true-ctx/s true-ctx/z)) 
            (hyp (knows-ctx/s knows-ctx/z) (true-ctx/s (true-ctx/s true-ctx/z)) (here refl)) 
            (⟦⟧I (knows-ctx/s (knows-ctx/s knows-ctx/z)) (true-ctx/s (true-ctx/s true-ctx/z)) (k-ctx/s-keep (k-ctx/s-keep k-ctx/z)) 
            (⊃E (knows-ctx/s (knows-ctx/s knows-ctx/z)) true-ctx/z 
              (hyp* (knows-ctx/s (knows-ctx/s knows-ctx/z)) true-ctx/z (there (here refl)))
              (hyp* (knows-ctx/s (knows-ctx/s knows-ctx/z)) true-ctx/z (here refl)))))))

  -- Known facts are true
  knownFactsAreTrue : ∀ {A a x u}
    → ([] , []) ⊢ (ƛ x ⇒ (let-box a ∣ u ≐ var x ⇒ var u)) ∶ ((⟦ a ⟧ A) ⊃ A) true
  knownFactsAreTrue = ⊃I knows-ctx/z true-ctx/z 
    (⟦⟧E knows-ctx/z (true-ctx/s true-ctx/z) (hyp knows-ctx/z (true-ctx/s true-ctx/z) (here refl)) 
      (hyp* (knows-ctx/s knows-ctx/z) (true-ctx/s true-ctx/z) (here refl)))

  -- Positive introspection
  introspection : ∀ {A a x u}
    → ([] , []) ⊢ (ƛ x ⇒ (let-box a ∣ u ≐ (var x) ⇒ (box a (box a (var u))))) ∶ ((⟦ a ⟧ A) ⊃ ⟦ a ⟧ (⟦ a ⟧ A)) true
  introspection = ⊃I knows-ctx/z true-ctx/z 
    (⟦⟧E knows-ctx/z (true-ctx/s true-ctx/z) 
      (hyp knows-ctx/z (true-ctx/s true-ctx/z) (here refl)) 
      (⟦⟧I (knows-ctx/s knows-ctx/z) (true-ctx/s true-ctx/z) (k-ctx/s-keep k-ctx/z) 
        (⟦⟧I (knows-ctx/s knows-ctx/z) true-ctx/z (k-ctx/s-keep k-ctx/z) 
        (hyp* (knows-ctx/s knows-ctx/z) true-ctx/z (here refl))))) 
