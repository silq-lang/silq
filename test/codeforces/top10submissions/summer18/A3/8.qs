namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : () 
    {
        body
        {
            mutable dif = 0;
            mutable pos = 0;
            let n= Length(qs);
            for (i in 0..n-1) {
                if (dif==0) {
                    if (bits0[i]==bits1[i]) {
                        if (bits0[i]==true) {
                            X(qs[i]);
                        }
                    } else {
                        set dif=1;
                        set pos=i;
                        H(qs[i]);
                    }
                } else {
                    if (bits0[i]==bits1[i]) {
                        if (bits0[i]==true) {
                            X(qs[i]);
                        }
                    } else {
                        CNOT(qs[pos],qs[i]);
                        if (bits0[i]!=bits0[pos]) {
                            X(qs[i]);
                        }
                    }
                }
            }
        }
    }
}