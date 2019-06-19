namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : ()
    {
        body
        {
            using (q=Qubit[5]) {
                CCNOT(x[0],x[1],q[0]);
                CCNOT(x[0],x[2],q[1]);
                CCNOT(x[1],x[2],q[2]);
                ApplyToEach(X,q[0..2]);
                CCNOT(q[0],q[1],q[3]);
                CCNOT(q[2],q[3],q[4]);
                CNOT(q[4],y);
                CCNOT(q[2],q[3],q[4]);
                CCNOT(q[0],q[1],q[3]);
                ApplyToEach(X,q[0..2]);
                CCNOT(x[1],x[2],q[2]);
                CCNOT(x[0],x[2],q[1]);
                CCNOT(x[0],x[1],q[0]);
                X(y);
            }
        }
    }
}