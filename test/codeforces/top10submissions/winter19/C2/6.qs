namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            // your code here
            let N = Length(x);
            if (N == 1)
            {
                X(y);
            }
            else
            {
            using (qs=Qubit[N])
            {
                for (p in 1..N-1)
                {
                    for (i in 0..N-p-1)
                    {
                        CNOT(x[i+p], x[i]);
                        X(x[i]);
                    }
                    Controlled X(x[0..N-p-1], qs[p]);
                    X(qs[p]);
                    for (i in N-p-1..-1..0)
                    {
                        X(x[i]);
                        CNOT(x[i+p], x[i]);
                    }
                }
                Controlled X(qs[1..N-1], y);
                X(y);

                for (p in 1..N-1)
                {
                    for (i in 0..N-p-1)
                    {
                        CNOT(x[i+p], x[i]);
                        X(x[i]);
                    }
                    X(qs[p]);
                    Controlled X(x[0..N-p-1], qs[p]);
                    for (i in N-p-1..-1..0)
                    {
                        X(x[i]);
                        CNOT(x[i+p], x[i]);
                    }
                }
            }
            }
        }
        adjoint auto;
    }
}