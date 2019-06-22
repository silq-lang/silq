namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[]) : () {
        body {
            let n = Length(x);
            mutable k = 1;
            X(x[0]);
            if (n == 1) {
                return ();
            }
            repeat {
                let last = 2 * k - 1;
                H(x[last]);
                for (i in 0..(k-2)) {
                    (Controlled X)([x[i]; x[last]], x[i + k]);
                }
                for (i in 0..(k-2)) {
                    (Controlled X)([x[last]; x[i + k]], x[i]);
                }
                for (i in 0..(k-2)) {
                    CNOT(x[i + k], x[last]);
                }
                CNOT(x[last], x[k - 1]);
                set k = k * 2;
            } until (k == n) fixup { }
        }
    }

    // operation Simulate(n : Int) : Int[] {
    //     body {
    //         mutable measurment = new Int[n];
    //         using (register = Qubit[n]) {
    //             let q = register;
    //             Solve(q);
    //             for (i in 0..(n-1)) {
    //                 if (M(q[i]) == One) 
    //                     { set measurment[i] = 1; }
    //             }
    //             ResetAll(register);
    //         }
    //         return measurment;
    //     } 
    // }
}
