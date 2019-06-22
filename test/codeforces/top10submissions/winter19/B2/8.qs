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
    //     using (q = Qubit())
    //     {
    //         mutable count = new Int[3];

    //         if (false) {
    //             Message("0 =============================");
    //             for (i in 0..4) {
    //                 Generate(0, q);
    //                 let v = Solve(q);

    //                 Reset(q);
    //             }
    //             Message("1 =============================");
    //             for (i in 0..4) {
    //                 Generate(1, q);
    //                 let v = Solve(q);

    //                 Reset(q);
    //             }
    //             Message("2 =============================");
    //             for (i in 0..4) {
    //                 Generate(2, q);
    //                 let v = Solve(q);

    //                 Reset(q);
    //             }
    //         }

    //         if (true) {
    //             for (i in 0 .. 100)
    //             {
    //                 Generate(i%3, q);
                
    //                 if (Solve(q) == i%3) {
    //                     Message($"Wrong on {i%3}");
    //                 }

    //                 Reset(q);
    //             }
    //         }
    //     }
    // }

    // operation Generate(ans: Int, q: Qubit) : Unit
    // {
    //     H(q);
    //     Rz(ToDouble(ans) * 2.0 * PI() / 3.0, q);
    // }

    operation Solve(q: Qubit) : Int
    {
        mutable r = 0;

        using (anc = Qubit())
        {
            H(q);
            CNOT(q, anc);
            S(anc);
            
            X(q);
            (Controlled Ry)([anc], (2.0*ArcCos(Sqrt(2.0/3.0)), q));
            CNOT(anc, q);
            
            let m1 = Measure([PauliZ, PauliZ], [q, anc]);

            // Collapsed to |00> + |11>
            if (m1 == Zero) {
                set r = 0;
            }
            else {
                // 0 -> |10>
                // 1 -> |10> + |01>
                // 2 -> |10> - |01>

                X(anc);
                CNOT(q, anc);

                H(q);

                if (M(q) == Zero) {
                    set r = 2;
                }
                else {
                    set r = 1;
                }

                //DumpRegister((), [q, anc]);
            }

            Reset(anc);
        }

        return r;
    }
}