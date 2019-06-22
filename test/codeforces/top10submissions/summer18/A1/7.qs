namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[]) : () {
        body {
            ApplyToEach(H(_), x);
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
