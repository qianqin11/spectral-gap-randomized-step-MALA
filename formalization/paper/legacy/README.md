# Legacy manuscript note

This directory preserves *A Detailed Davies-Perturbation Proof for Stationary
Langevin Increments*, an earlier standalone companion note by Qian Qin.  It
develops the continuous-time Davies-perturbation argument that underlies the
stationary Langevin increment estimate used in the Uniform Random MALA paper.

The current paper is [`../main.tex`](../main.tex), with bibliography
[`../uniform_random_mala.bib`](../uniform_random_mala.bib).  Its Appendix B
contains the paper's current continuous-time rejection/overlap proof.  The
companion files here are retained only for their more focused standalone
exposition and are not part of the current manuscript or the Lean dependency
chain.  In particular, the Lean formalization proves the corresponding
rejection and overlap results through a finite discrete approximation and
weak-limit argument rather than by formalizing this continuous-time note.

Files:

- `davies_perturbation_companion_note.tex`: source of the historical note;
- `davies_perturbation_companion_note.bib`: its bibliography;
- `davies_perturbation_companion_note.pdf`: previously compiled rendering.
