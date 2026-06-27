# Translation Templates for Dedukti

[Dedukti](https://github.com/Deducteam/Dedukti) is a proof language based on the λΠ-calculus modulo theory, that is λ-calculus with dependent types and user-defined rewrite rules. 

This tool helps users to perform generic translations inside Dedukti. The three translation templates are:
- theory morphisms from a source theory to a target theory [RS13, TR25],
- logical relations over a theory morphism [RS13, TR25],
- theory embeddings of a source theory into a target theory [Tra24].


## Requirements

- Opam and OCaml

- Install [Dedukti](https://github.com/Deducteam/Dedukti?tab=readme-ov-file#install-with-opam) with Opam.


## How to use it?

1. Clone and enter this repository:
```
git clone https://github.com/Deducteam/TranslationTemplates
cd TranslationTemplates
```

2. To apply a translation template, run 
```
bash translate.sh template source.dk target.dk result.dk
```
where 
- `template` indicates the template to use (`morphism`, `relation` or `embedding`),
- `source.dk` is the Dedukti file of the source theory,
- `target.dk` is the Dedukti file of the target theory,
- `result.dk` is the file containing the output of the translation.

You have to replace the `TODO`s by correct parameters inside `result.dk`. 

You can check `result.dk` automatically. As this Dedukti file depends on `target.dk`, we need to generate the object file `target.dko`.
```
dk check -e target.dk
dk check result.dk
```
For `result.dk` to typecheck, the conditions on the parameters must be satisfied. 
The conditions on the constants are checked by Dedukti, but the conditions on the rewrite rules are left to be checked by the users.


## Examples

You can find several examples of theory morphisms, logical relations and theory embeddings in the folder `examples`. These examples include:
- theory morphisms between the multiplication group and the division group,
- a theory morphism from classical logic to intuitionistic logic,
- a theory morphism from deduction-style to computation-style,
- a theory morphism from propositional logic to Q0 logic,
- a theory morphism from lists to binary trees,
- a theory morphism between different subsets of connectives,
- a theory morphism from hard-sorted logic to soft-sorted logic,
- a theory morphism from soft-sorted logic to unsorted logic,
- a theory morphism from natural numbers to integers,
- a theory morphism and logical relation from the Church to the Curry encoding.


## References

[RS13] Florian Rabe and Kristina Sojakova. 2013. Logical relations for a logical framework. ACM Transactions on Compututational Logic 14, 4, Article 32, 34 pages. https://doi.org/10.1145/2536740.2536741

[Tra24] Thomas Traversié. 2024. Proofs for Free in the λΠ-Calculus Modulo Theory.  Proceedings Workshop on Logical Frameworks and Meta-Languages: Theory and Practice (LFMTP 2024), EPTCS 404, pp. 49–63. https://doi.org/10.4204/EPTCS.404.4

[TR25] Thomas Traversié and Florian Rabe. 2025. Formalizing Representation Theorems for a Logical Framework with Rewriting. https://arxiv.org/abs/2504.07537
