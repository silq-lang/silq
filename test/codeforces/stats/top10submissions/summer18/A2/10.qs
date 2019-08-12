namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;
    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
            mutable i = -1;
            let N = Length(bits);
            for(j in 0..N-1){
                if(bits[j]){
                    set i=j;
                }
            }
            H(qs[i]);
            for(j in 0..N-1){
                if(j!=i && bits[j]){
                    CNOT(qs[i],qs[j]);
                }
            }
        }
    }
}