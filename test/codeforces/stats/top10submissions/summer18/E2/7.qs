namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation fun(x : Qubit[], y : Qubit) : () {
    //     body {
    //         CNOT(x[0], y);
    //     }
    // }

    // operation one(x : Qubit[], y : Qubit) : () {
    //     body {
    //         ApplyToEach(CNOT(_, y), x);
    //     }
    // }

    operation Solve (n : Int, f : ((Qubit[], Qubit) => ())) : Int[] {
        body {
            mutable res = new Int[n];
            using (reg = Qubit[n + 1]) {
                let x = reg[0..(n-1)];
                let y = reg[n];

                f(x, y);

                mutable sum = 0;
                if (M(y) == One) {
                    set sum = sum + 1;
                }

                if (n % 2 == 1) {
                    set sum = sum + 1;
                }

                if (sum % 2 == 1) {
                    set res[0] = 1;
                }
                
                ResetAll(reg);
            }
            return res;
        }
    }

    // operation Simulate(n : Int) : Int[] {
    //     body {
    //         return Solve(n, fun);
    //     } 
    // }
}
