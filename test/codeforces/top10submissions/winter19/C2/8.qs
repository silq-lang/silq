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
    //     using ((qs, ans) = (Qubit[3], Qubit()))
    //     {
    //         X(qs[0]);
    //         //H(qs[1]);
    //         //H(qs[2]);

    //         DumpRegister((), qs);

    //         Solve(qs, ans);

    //         DumpRegister((), qs + [ans]);

    //         ResetAll(qs);
    //         Reset(ans);
    //     }
    // }

    operation Solve (x : Qubit[], y : Qubit) : Unit 
    {
        body (...) 
        {
            let xlen = Length(x);

            // max 6 period
            using (anc = Qubit[6])
            {
                for (period in 1 .. MinI(6, xlen-1)) {
                    for (i in 0 .. period-1) {
                        for (j in 1 .. 6) {
                            if (i + j*period < xlen) { CNOT(x[i], x[i+j*period]); }
                        }
                    }
                    
                    ApplyToEachA(X, x[period..xlen-1]);
                    
                    //Message($"Period {period}");
                    //DumpRegister((), x + anc[1..1]);
                    (Controlled X)(x[period..xlen-1], anc[period-1]);
                        
                    ApplyToEachA(X, x[period..xlen-1]);

                    // UNCOMPUTE
                    for (i in 0 .. period-1) {
                        for (j in 1 .. 6) {
                            if (i + j*period < xlen) { CNOT(x[i], x[i+j*period]); }
                        }
                    }
                }
                
                //Message($"P1: {M(anc[0])}");
                //Message($"P2: {M(anc[1])}");
                //Message($"P3: {M(anc[2])}");
                //Message($"P4: {M(anc[3])}");
                //Message($"P5: {M(anc[4])}");
                //Message($"P6: {M(anc[5])}");

                ApplyToEachA(X, anc);

                (Controlled X)(anc, y);
                X(y);

                // UNCOMPUTE
                ApplyToEachA(X, anc);
                
                for (period in 1 .. MinI(6, xlen-1)) {
                    for (i in 0 .. period-1) {
                        for (j in 1 .. 6) {
                            if (i + j*period < xlen) { CNOT(x[i], x[i+j*period]); }
                        }
                    }
                    
                    ApplyToEachA(X, x[period..xlen-1]);
                        
                    (Controlled X)(x[period..xlen-1], anc[period-1]);
                        
                    ApplyToEachA(X, x[period..xlen-1]);

                    // UNCOMPUTE
                    for (i in 0 .. period-1) {
                        for (j in 1 .. 6) {
                            if (i + j*period < xlen) { CNOT(x[i], x[i+j*period]); }
                        }
                    }
                }
            }
        }
        adjoint auto;
    }
}