namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
            let N = Length(qs);
            H(qs[0]);
            for (i in 1..N-1) {
                if (bits[i]==true) {
                    CNOT(qs[0],qs[i]);
                }
            }
            if (bits[0]==false) {
                H(qs[0]);
            }
            // your code here
        }
    }
}

