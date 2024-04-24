# Light Intro to Formal Logic, Proof Systems, Theorem Proving

## Formal Logic

> Formal logic is the science of deductively valid inferences or logical truths. It studies how conclusions follow from premises due to the structure of arguments alone, independent of their topic and content.

## [Proof Systems](https://en.wikipedia.org/wiki/Proof_calculus)

Hilbert-style systems and Gentzen-style systems.

Gentzen's [Natural Deduction](https://en.wikipedia.org/wiki/Natural_deduction) is a pretty neat one.


### Natural Deduction for First-order Predicate Logic in "Fitch-style Notation"


#### Fitch-style Notation
```
| <PREMISE 1>
| <PREMISE 2>
| ...
| <PREMISE N>
|--------------- <rule-name>
| <CONCLUSION>
```




#### Conjunction Introduction
```
| A
| B
|-------- conj-intro
| A ∧ B
```


#### Conjunction Elimination

```
| A ∧ B
|-------- conj-elim-l
| A
```

```
| A ∧ B
|-------- conj-elim-r
| B
```


#### Disjunction Introduction
```
| A
|------------- disj-intro-l
| A ∨ B
```

```
| B
|------------- disj-intro-r
| A ∨ B
```


#### Disjunction Elimination
```
| A ∨ B
| 
|   | A
|   |----
|   | C
| 
|   | B
|   |----
|   | C
|--------- disj-elim
| C
```


#### Implication Introduction
```
  | A
  |-----
  | B

--------- impl-intro
A ==> B
```


#### Implication Elimination
```
| A ==> B
| A
|---------- impl-elim
| B
```


#### Negation Introduction
```
| | A
| |-----
| | ⊥
|
|-------------- neg-intro
| ¬A
```


#### Negation Elimination
```
| A
| ¬A
|--------- neg-elim
| ⊥
```

#### Contradiction Elimination
```
| ⊥
|------ contra-elim
| A
```

#### Proof by Contradiction
```
| | ¬A
| |-----
| | ⊥
|----------- proof-by-contra
| A
```


#### Forall Introduction
```
| | x
| |-------
| | P[x]
|------------- forall-intro
| ∀ α P[x/α]
```
As a side-condition—the `x` must not "escape" its scope.

> Demonstrate.


#### Forall Elimination
```
| ∀ α P[α]
|------------- forall-elim
| P[α/x]
```


#### Exists Introduction
```
| P[t]
|------------ exists-intro
| ∃ α P[t/α]
```
As a side note—not all occurrences of term `t` have to be replaced with `α`s.

> Demonstrate.


#### Exists Elimination
```
| ∃ α P[α]
|
| | P[α/x]
| |-------
| | F
|
|----------- exists-elim
| F
```

As a side-condition—the `x` must not "escape" its scope.


> Do these resemble something you know? Maybe focus on the implication introduction and elimination, forall introduction ...

## Theorem Proving

Theorem proving is not magic!

> Let's do some light theorem proving.


______

### Sometimes, a little bit of magic is nice, though.


![](can-we-have-induction.png)
