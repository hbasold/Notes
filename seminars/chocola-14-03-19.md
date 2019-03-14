# Filip Sieczkowski -- Abstraction and Equational Reasoning for Algebraic Effects and Handlers #

## Introduction ##

* Moggi '88: Category C of values and Kleisli category for a monad on C to
  interpret computations
* Doesn't scale well to multi-effect computations (monad transformers)
* Plotkin & Power: use algebraic theories instead (*algebraic effects*)
  * Important property: K[op x] == let v = op x in K[v]
  * *Operation can be performed outside of context*
* Effectful computations are trees of operations
  * operations remain uninterpreted
  * tree may be reduced by using an algebra for the theory
* Question: Are all effects algebraic?
  * No: Continuation has no finitary algebraic characterisation
  * Throwing exceptions is fine; catching is however not well-behaved because
    it removes an effect
* Plotkin & Pretnar '09: *Handlers* arise from algebras to model catching
  exceptions (and more)
* **However**: Algebraic specification is lost in the process!
  * -> We would need dependent type to express equality
  * **Apply our work on HITs to algebraic effects!**
* Paper at POPL'18 (limited calculus) and POPL'19 on programming
* Coq implementation and experimental language

## Semantic Choices ##

* Barebones effects: single operation *do*; handler expression
  *handle e with a, r. e1; x. e2*; operation matches nearest enclosing handler
* handle K[do v] with a, r. e1; x. e2 |-> e1[v/a, u/r], where either
  * u = λz. handle K[z] with a, r. e1; x. e2, or
  * u = λz. K[z]
  * *Deep* and *shallow* handlers (related to shift delimited control operator)

### Example ###

    handle
      "Hello" ++ do () ++ "! How are you " ++ do () "?"
    with
      (), r. r "Dave";
      x. x

With deep handlers, we get the expected behaviour.
To get the same with shallow handlers, we would have to implement a recursive
function that emulates the behaviour by calling itself and do the replacement.

### Other design choices ###
  * Multiple operations
  * Labelled effects: allows jumping to arbitrary handlers; cf. multi-prompt
    delimited control; example: combining error and reader effect

**Here: multi-op, labelled, deep handlers**

## Problems of Parametricity ##

* A variant map' of map that uses internally an effect Tick and handles it
* If we call it with a function f that uses the same effect but does not handle
  the effect
* Then map' accidentally handles the effect Tick of f
* *Question*: Is map' parametric?
* Current research question: How do these interaction behave?

## Type-and-Effect System for Algebraic Effects

* Record effects of computation to constrain behaviour
* Includes quantification over types and effects for polymorphism
  * Constraint: computation may not perform an effect
* Function space is annotated with effects: ->[γ]
* Example
  * map : ∀α β γ. (α ->[γ] β) -> list α ->[γ] list β
  * map' : ∀α β γ. (α ->[Tick, γ] β) -> list α ->[γ] list β
  * Note that the type of map' is less general because f in map' f
    needs to handle the effect Tick for arguments!
  * Subtyping that would remove Tick would break parametricity

## Effect Abstraction: Union-Find ##

* Allows implementation of unification
* Using existential quantification over effects:


    sig
        type Set  : type -> type
        type UF   : type -> effect

        val new : a ->[UF a] Set a
        val find : Set a ->[UF a] a
        val union : (a -> a ->[e] a) ->
                    Set a -> Set a ->[UF a, e] Unit
        val handleUF : (Unit ->[UF a, e] v) ->[e] v

* This gives two problems (which?)
* Can be solved with coercions (not very nice)
  * affect dynamic semantics
  * cannot be subtyping, as that would break parametricity
* Coercions embody weakening, exchange, contraction
  * Thus, indexing into context

## Equivalence of Effectful Code ##

f : ∀α. (1 ->[α] σ) -> γ |-
    f (λz. 5) ~ f (λz. ask ())

* *Logical relations* for effectful computations
  * Usual things for Unit, Int
  * (v1, v2) ∈ [[A ->[E] B]](θ) iff
    ∀(u1, u2) ∈ [[A]](θ). (v1 u1, v2 u2) ∈ **[[E]]** [[B **/ E**]](θ)
  * Similar for universal quantification
* Adapt biorthoginality:
  * (e1, e2) ∈ [[E]] [[A / E]](θ) iff
    ∀(K1, K2) ∈ [[K]] [[A / E]](θ) (K1[e1], K2[e2]) ∈ Obs
  * (K1, K2) ∈ [[K]] [[A / E]](θ) iff
    ∀(v1, v2) ∈ [[A]](θ). (K1[v1], K2[v2]) ∈ Obs
    and ∀(e1, e2) ∈ [[S]] [[A / E]](θ). (K1[e1], K2[e2]) ∈ Obs
  * (K1[e1], K2[e2]) ∈ [[S]] [[A / E]](θ) iff
     ∃μ. (e1, e2, μ) ∈ [[E]](θ)
       and ∀(e1', e2') ∈ μ. (K1[e1'], K2[e2']) ∈ [[E]] [[A / E]](θ)
       and K1, K2 [....]
  * e1 and e2 are control stuck (operation applied to value), μ is relation on
    output
  * Well-defined by using step-indexing (not needed with non-recursive effects)

* Prove λx. 5 ~ λx. ask () : Unit ->[α] Int
  * Pick R = {(5, ask(), {(5, 5)})}
  * This enforces that a handler of ask returns 5 when the computation 5 is
    performed
  * In the equivalence proof, ask () is replaced by 5

* Can be used to prove that default action (*finally* block) is not necessary,
  if we have coercions:

    handle(E) e with ... | return x. f end
    ~ handle (λx. <lift E> f) e with ... end

## Future ##
* Coercions unsatisfactory, need better approach
* Compilation, optimisation etc.
* Typed CPS translations?
* Back to logic and semantics:
  * relating calculi to λμ/System L
  * semantics in style of Moggi
  * Curry-Howard view of algebraic effects?
* Further exploration of relationship with control operators

## Questions ##
* Can we recover a nice presentation for languages with multi-op, labelled,
  deep handlers languages
  * Free algebra for algebraic theory
  * Higher-order? (Ambroise)
  * Dependent operations?
  * Recursive effects lead to completely iterative monads instead of
    algebras for algebraic theory
* Meta-language for coercions with names for effects or de Bruijn indices
  * effect framework, like LF?
