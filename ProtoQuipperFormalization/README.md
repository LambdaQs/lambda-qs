# Formalization of Metatheory of the Quipper Quantum Programming Language in a Linear Logic

By Mohamed Yousri Mahmoud and Amy P. Felty

Home: https://www.site.uottawa.ca/~afelty/jar19/

## Building
Only works up to Coq 8.10.2.

First time setup to get the right version of Coq:
```bash
opam switch create 4.09.1
eval $(opam env)
opam pin add coq 8.10.2
```

Then the usual `make`.
