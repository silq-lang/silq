namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Testing;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Extensions.Convert;

    // operation SolveTest() : Unit 
    // {
    //     using ((qs, ans) = (Qubit[4], Qubit()))
    //     {
    //         H(qs[0]);
    //         H(qs[1]);
    //         H(qs[2]);
    //         H(qs[3]);

    //         DumpRegister((), qs);

    //         Solve(qs, ans);

    //         DumpRegister((), qs + [ans]);

    //         ResetAll(qs);
    //         Reset(ans);
    //     }
    // }

    operation Rotate(anc: Qubit[], temp: Qubit) : Unit
    {
        body (...) 
        {
            SWAP(anc[2], temp);
            SWAP(anc[2], anc[1]);
            SWAP(anc[1], anc[0]);
            SWAP(anc[0], temp);
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }
    operation Solve (x : Qubit[], y : Qubit) : Unit 
    {
        body (...) 
        {
            using ((anc, temp) = (Qubit[3], Qubit()))
            {
                X(anc[0]);

                for (q in x) {
                    (Controlled Rotate)([q], (anc, temp));
                }

                ApplyToEachA(X, [anc[0]]);
            
                X(y);
                (Controlled X)([anc[0]], y);

                ApplyToEachA(X, [anc[0]]);

                for (q in x) {
                    (Adjoint Controlled Rotate)([q], (anc, temp));
                }

                X(anc[0]);
            }
        }
        adjoint auto;
    }
}