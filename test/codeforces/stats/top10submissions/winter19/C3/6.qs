namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation addU(x : Qubit[]): Unit {
        
    //     controlled auto;
    //     adjoint auto;
    // }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            using (anc=Qubit[2])
            {
                for (i in 0..Length(x)-1)
                {
                    X(anc[1]);
                    CCNOT(x[i], anc[1], anc[0]);
                    X(anc[0]);
                    X(anc[1]);
                    CCNOT(x[i], anc[0], anc[1]);
                    X(anc[0]);
                }
                X(anc[0]);
                X(anc[1]);
                Controlled X(anc, y);
                X(anc[0]);
                X(anc[1]);
                for (i in 0..Length(x)-1)
                {
                    X(anc[0]);
                    CCNOT(x[i], anc[0], anc[1]);
                    X(anc[1]);
                    X(anc[0]);
                    CCNOT(x[i], anc[1], anc[0]);
                    X(anc[1]);
                }
            }
        }
        adjoint auto;
    }
}