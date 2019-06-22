namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], b : Bool[], c : Bool[]) : () {
        body {
            let n = Length(x);
            mutable at = 0;
            for (i in 0..(n-1)) {
                if (b[i] != c[i]) {
                    set at = i;
                }
            }

            H(x[at]);

            for (i in 0..(n-1)) {
                if (i != at && b[i] != c[i]) {
                    CNOT(x[at], x[i]);
                }
            }

            for (i in 0..(n-1)) {
                if (b[i]) {
                    X(x[i]);
                }
            }
        }
    }

    // operation Simulate(n : Int) : Int[] {
    //     body {
    //         mutable measurment = new Int[n];
    //         mutable b = new Bool[n];
    //         for (i in 0..(n-1)) {
    //             if (i % 3 == 0) {
    //                 set b[i] = true;
    //             }
    //         }
    //         mutable c = new Bool[n];
    //         for (i in 0..(n-1)) {
    //             if (i % 2 == 0) {
    //                 set c[i] = true;
    //             }
    //         }
    //         using (register = Qubit[n]) {
    //             let q = register;
    //             Solve(q, b, c);
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
