namespace TinyExample {
    open Microsoft.Quantum.Intrinsic;

    operation ApplyH (q : Qubit) : Unit {
        H(q);
    }

    operation ApplyX (q : Qubit) : Unit is Adj+Ctl {
        X(q);
    }

    operation ApplyCNOT (q1 : Qubit, q2 : Qubit) : Unit {
        CNOT(q1, q2);
    }
}
