# Formaldehyde
NK/LK lightweight interactive proof assistant

## Requirements

An OCaml distribution (v4.x or whatever), with `OCamlMakeFile` in your `make` path (or simply a copy of it in the Formaldehyde directory).

*NB:* Formaldehyde uses the `Unix` OCaml standard module to detect whether the input is a terminal or a redirection. According to the OCaml documentation, this should be correctly emulated under Windows (however, this was not tested).

Compiling:
```
$ make
```

## Contents

### Implemented features
- full NK sequent-based (**à la** Gentzen) proof system
- proof tree export to LaTeX

### ToDo list
- fix the current parser priorities that are not standard
- fix the parentheses printing (currently incomplete, and should be implemented in accordance to the parser priorities)
- LK proof system
- basic automatic proof search algorithm

### On proof tree export to LaTeX

There are many LaTeX packages that provide macros to build proof trees. Formaldehyde currently uses the rather classical LaTeX package `proof` (simple an classical tree-based syntax, nice aesthetics, after having considered the slightly less satisfactory `mathpartir` package).

For a somehow more "modern" approach, one could also consider more recent packages such as `bussproofs` or `ebproofs` that provide a **stack-based** syntax (or **reverse Polish** style).

## Syntax

**syntax documentation coming soon...**

## References

- a [good textbook](http://www.lama.univ-savoie.fr/~raffalli/dnr/) (in french) on the subject
- [Natural deduction](https://en.wikipedia.org/wiki/Natural_deduction) on Wikipedia
- [Sequent calculus](https://en.wikipedia.org/wiki/Sequent_calculus) on Wikipedia
