namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        mutable anc = qs;
        for (i in 0..Length(qs)-1) {
            set anc[i] = qs[(i+Length(qs)-1)%(Length(qs))];
        }

        X(qs[Length(qs)-1]);
        for (i in Length(qs)-2..-1..0) {
            Controlled  X(anc[0..i], qs[i]);
        }
        X(qs[Length(qs)-1]);

        for (i in 0..Length(qs)-2) {
            X(qs[i]);
        }

        for (i in Length(qs)-2..-1..0) {
            (Controlled X) (anc[0..i], qs[i]);
        }
        for (i in 0..Length(qs)-2) {
            X(qs[i]);
        }
        X(qs[Length(qs)-1]);
        for (i in 1..Length(qs)-1) {
            CNOT(qs[0],qs[i]);
        }
        H(qs[0]);
        for (i in 1..Length(qs)-1) {
            CNOT(qs[0],qs[i]);
        }
    }
}