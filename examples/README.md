# Some Examples of Translations

We present here some translations performed using the three templates, with appropriate parameters.


## Theory morphisms

- *Between different subsets of connectives*: `connectives_and_all.dk` uses the conjunction and the universal quantifier, while `connectives_or_ex.dk` uses the disjunction and the existential quantifier. `morphism_connectives.dk` presents a theory morphism from `connectives_and_all.dk` to `connectives_or_ex.dk`.

- *From classical logic to intuitionistic logic*: `classical.dk` uses classical higher-order logic while `intuitionistic.dk` uses intuitionistic higher-order logic. `morphism_classical_intuitionistic.dk` presents a theory morphism from `classical.dk` to `intuitionistic.dk`.

- *From deduction to computation*: `deduction.dk` uses axioms to represent natural deduction rules while `computation.dk` uses rewrite rules to represent natural deduction rules. `morphism_deduction_computation.dk` presents a theory morphism from `deduction.dk` to `computation.dk`.


## Logical relations

- *From the Church to the Curry encoding*: `church.dk` uses the Church encoding of simple type theory while `curry.dk` uses the Curry encoding. `relation_church_curry.dk` presents a logical relation between `church.dk` and `curry.dk`.


## Theory embeddings

- *Of natural numbers into integers*: `nat.dk` uses natural numbers while `int.dk` uses intergers. `embedding_nat_int.dk` presents a theory embedding of `nat.dk` into `int.dk`.

- *Of sorted logic into unsorted logic*: `sorted.dk` uses sorted logic while `unsorted.dk` uses unsorted logic. `embedding_sorted_unsorted.dk` presents a theory embedding of `sorted.dk` into `unsorted.dk`.