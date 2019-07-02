namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Convert;
    open Microsoft.Quantum.Extensions.Math;
    operation Solve (q : Qubit) : Int
    {
        body
        {
            mutable output = 0;
            let basis = RandomInt(2);
            // randomize over std and had
            if (basis == 0) {
                // use standard basis
                let result = M(q);
                if (result == One) {
                    // this can only arise if the state was |+>
                    set output = 1;
                }
                else {
                    set output = -1;
                }
            }
            else {
                // use Hadamard basis
                H(q);
                let result = M(q);
                if (result == One) {
                    // this can only arise if the state was |0>
                    set output = 0;
                }
                else {
                    set output = -1;
                } 
            }
            return output;
        }
    }
}