namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            let n=Length(qs);
            X(qs[0]);
            mutable s=1;
            for (it in 0..n) {
                if (s!=n) {
                    using (q=Qubit[1]) {
                        H(q[0]);
                        for (i in 0..s-1) {
                            CCNOT(q[0],qs[i],qs[i+s]);
                            CCNOT(q[0],qs[i+s],qs[i]);
                        }
                        for (i in 0..s-1) {
                            CNOT(qs[i+s],q[0]);
                        }
                    }
                    set s=s*2;
                }
            }
        }
    }
}