namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
            let n = Length(qs);
            mutable diff = -1;
            mutable idx = 0;
            repeat {
                if (bits0[idx] != bits1[idx]) {
                    set diff = idx;
                }
                else {
                    if (bits0[idx]) {
                        X(qs[idx]);
                    }
                    set idx = idx + 1;
                }
            } until diff != -1
            fixup {
                
            }

            H(qs[diff]);
            let b = bits0[diff];

            for (i in diff+1..n-1) {
                if (bits0[i] == bits1[i]) {
                    if (bits0[i]) {
                        X(qs[i]);
                    }
                }
                else {
                    let k = b != bits0[i];
                    CNOT(qs[diff], qs[i]);
                    if (k) {
                        X(qs[i]);
                    }
                }
            }
        }
    }
}