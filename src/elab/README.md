# Requirements
- [BNF Converter](https://github.com/BNFC/bnfc): `cabal install BNFC` (I am using BNFC v2.9.4).
- `opam install menhir utop`

# Build and run using:

```
make
./TestLambdaQs
```

The binary lets us enter expressions, pressing Ctrl-D will parse them and exit the app. One can also pass input through stdin:

```
$ echo "cmd Controlled X (q1, q2)" | ./TestLambdaQs
[Abstract syntax]

ECmd (CCap (MUni (Ident "X"), EVar (MVar (Ident "q1")), EVar (MVar (Ident "q2"))))

[Linearized tree]

cmd Controlled X (q1, q2)
```

# Extending the source
`make genclean` will clean up most of the auto-generated files except those by `bnfc`. Write modules assuming existence of the remaining source files which include those for the AST, the lexer and the parser specs, the print and show infrastructure, etc.

# Example from PLanQC:

## Sugared Syntax

This is what is currently encoded in the file

```
cmd dcl q in
ret let q1 be &q in
let q2 be q1 in
cmd Controlled X (q1, q2)
```

Output AST:

`ECmd (CDcl (MQey (Ident "q"), CRet (ELet (MVar (Ident "q1"), EQloc (MQey (Ident "q")), ELet (MVar (Ident "q2"), EVar (MVar (Ident "q1")), ECmd (CCap (MUni (Ident "X"), EVar (MVar (Ident "q1")), EVar (MVar (Ident "q2")))))))))`

## Core Syntax

If you'd like to try this style, you will need to switch to [the first version of the grammar](https://github.com/k4rtik/lambda-qs/blob/4ff004152b75e99b95a828901479471e30c5749b/src/elab/LambdaQs.cf).

`cmd(dcl(q.ret(let(qloc[q];q1.let(q1;q2.cmd(ctrlapr(q1;q2;X)))))))`

Output:

`ECmd (CDcl (MSym (Ident "q")) (CRet (ELet (EQloc (MSym (Ident "q"))) (MVar (Ident "q1")) (ELet (EVar (MVar (Ident "q1"))) (MVar (Ident "q2")) (ECmd (CCap (EVar (MVar (Ident "q1"))) (EVar (MVar (Ident "q2"))) (MUni (Ident "X"))))))))`
