# Some Examples of Translations

We present here some translations performed using the three templates, with appropriate parameters.


## Theory morphisms

- *Between the multiplication group and the division group* (folder `groups`): `mulGr` represents the multiplication group while `divGr` represents the same group defined with a division symbol. `morphism_mulGr_divGr.dk` presents a theory morphism from `mulGr.dk` to `divGr.dk`, `morphism_divGr_mulGr.dk` presents a theory morphism from `divGr.dk` to `mulGr.dk`, and `morphism_mulGr_mulGr.dk` presents a theory morphism from `mulGr.dk` to itsfelf.

- *From propositional logic to Q0 logic* (folder `propositional_q0`): `impand.dk` encodes propositional logic while `q0.dk` encodes Q0 higher-order logic. `morphism_impand_q0.dk` presents a theory morphism from `impand.dk` to `q0.dk`.

- *From lists logic to binary trees* (folder `list_tree`): `list.dk` encodes the data structure of list while `tree.dk` encodes the data structure of binary tree. `morphism_list_tree.dk` presents a theory morphism from `list.dk` to `tree.dk`.

- *From classical logic to intuitionistic logic* (folder `classical_intuitionistic`): `classical.dk` encodes higher-order classical logic while `intuitionistic.dk` encodes higher-order intuitionistic logic. `morphism_classical_intuitionistic.dk` presents a theory morphism from `classical.dk` to `intuitionistic.dk`.

- *From deduction to computation* (folder `deduction_computation`): `deduction.dk` uses axioms to represent natural deduction rules while `computation.dk` uses rewrite rules to represent natural deduction rules. `morphism_deduction_computation.dk` presents a theory morphism from `deduction.dk` to `computation.dk`.

- *Between different subsets of connectives* (folder `connectives`): `connectives_and_all.dk` uses the conjunction and the universal quantifier, while `connectives_or_ex.dk` uses the disjunction and the existential quantifier. `morphism_connectives.dk` presents a theory morphism from `connectives_and_all.dk` to `connectives_or_ex.dk`.

- *From hard-sorted logic to soft-sorted logic* (folder `hardsorted_softsorted_unsorted`): `hardsorted.dk` encodes hard-sorted logic while `softsorted.dk` encodes soft-sorted logic. `morphism_hardsorted_softsorted.dk` presents a theory morphism from `hardsorted.dk` to `softsorted.dk`.

- *From soft-sorted logic to unsorted logic* (folder `hardsorted_softsorted_unsorted`): `softsorted.dk` encodes soft-sorted logic while `unsorted.dk` encodes unsorted logic. `morphism_softsorted_unsorted.dk` presents a theory morphism from `softsorted.dk` to `unsorted.dk`.

- *From natural numbers to integers* (folder `nat_int`): `nat.dk` uses natural numbers while `int.dk` uses intergers. `morphism_nat_int.dk` presents a theory morphism from `nat.dk` to `int.dk`.


## Logical relations

- *From the Church to the Curry encoding* (folder `church_curry`): `church.dk` uses the Church encoding of simple type theory while `curry.dk` uses the Curry encoding. `relation_church_curry.dk` presents a logical relation between `church.dk` and `curry.dk`.


## Theory embeddings

- *From natural numbers to integers* (folder `nat_int`): `nat.dk` uses natural numbers while `int.dk` uses intergers. `embedding_nat_int.dk` presents a theory embedding from `nat.dk` to `int.dk`.
