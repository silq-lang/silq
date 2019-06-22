namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], b : Bool[]) : () {
        body {
            H(x[0]);
            let n = Length(x);
            for (i in 1..(n-1)) {
                if (b[i]) {
                    CNOT(x[0], x[i]);
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
    //         using (register = Qubit[n]) {
    //             let q = register;
    //             Solve(q, b);
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
