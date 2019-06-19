// make sure to reset qubits to zero!
// quick reference: https://assets.codeforces.com/rounds/997-998/qs-language-quick-reference.pdf

namespace Solution
{
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Primitive;

    operation Set (desired: Result, q1: Qubit) : ()
    {
        body
        {
            let current = M(q1);
            if (desired != current) { X(q1); }
        }
    }

    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
            for (i in 0..Length(qs)-1) {
                Set(Zero,qs[i]);
            }
            
            mutable pos = 0;
            for (i in 0..Length(qs)-1) {
                if (bits0[i] != bits1[i]) {
                    set pos = i;
                }
            }

            H(qs[pos]);
            for (i in 0..Length(qs)-1) {
                if (i != pos && bits0[i] != bits1[i]) {
                    CNOT(qs[pos],qs[i]);
                }
            }
            
            for (i in 0..Length(qs)-1) {
                if (bits0[i] == true) {
                    X(qs[i]);
                }
            }
        }
    }
}