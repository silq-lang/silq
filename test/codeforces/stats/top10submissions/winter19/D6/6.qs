namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Convert;

    operation Deal(qs : Qubit[], V : Int) : Unit {
        body (...) {
            let binarypoint = BigIntToBools(ToBigInt(V));
            for (i in 0..Length(binarypoint)-1) 
            {
                if (binarypoint[i] == true) 
                {
                    for (j in Length(qs)-1..-1..i)
                    {
                        Controlled X(qs[i..j-1], qs[j]);
                    }
                }
            }
        }
        adjoint auto;
    }
    operation Solve (qs : Qubit[]) : Unit {
        let N = 2^Length(qs);
        for (i in N-2..-1..0) {
            Adjoint Deal(qs, i);
            for (j in 1..Length(qs)-1) {
                X(qs[j]);
            }
            (Controlled H) (qs[1..Length(qs)-1], qs[0]);
            for (j in 1..Length(qs)-1) {
                X(qs[j]);
            }
            Deal(qs, i);
        }
    }
}