namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            using ((c0, c1) = (Qubit(), Qubit())) {
                X(c0);
                X(c1);
                for (q in x) {
                    CCNOT(q, c1, c0);
                    CCNOT(q, c0, c1);
                }
                CCNOT(c0, c1, y);
                for (q in x) {
                    CCNOT(q, c0, c1);
                    CCNOT(q, c1, c0);
                }
                X(c0);
                X(c1);
            }
        }
        adjoint auto;
    }
}