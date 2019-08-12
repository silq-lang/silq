namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Spread (qs : Qubit[]) : ()
    {
        body
        {
            let n = Length(qs);
            if (n != 1) {
                let m = n / 2;
                (Controlled H)([qs[0]], qs[m]);
                CNOT(qs[m], qs[0]);
                Spread(qs[0..m-1]);
                Spread(qs[m..n-1]);
            }
        }
    }

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            X(qs[0]);
            Spread(qs);
        }
    }
}