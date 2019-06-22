namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;

    operation Solve (x : Qubit) : Int {
        body {
            Ry(PI() / 8., x);
            if (M(x) == One) {
                return 1;
            } else {
                return 0;
            }
        }
    }

    // operation Simulate(n : Int) : Int {
    //     body {
    //         mutable measurment = 0;
    //         using (register = Qubit[1]) {
    //             let x = register[0];
    //             if (n == 1) {
    //                 H(x);
    //             }
    //             set measurment = Solve(x);
    //             ResetAll(register);
    //         }
    //         return measurment;
    //     } 
    // }
}
