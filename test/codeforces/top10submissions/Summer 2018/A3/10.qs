
namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;
   operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
            mutable i = -1;
            mutable ii = -1;
            let N = Length(bits0);
            for(j in 0..N-1){
                if((!bits0[j]) && bits1[j]){
                    set i=j;
                }
                if((!bits1[j]) && bits0[j]){
                    set ii=j;
                }
            }
            for(j in 0..N-1){
                if(bits0[j] && bits1[j]){
                    X(qs[j]);
                }
            }
            if(i != -1){
                H(qs[i]);
                for(j in 0..N-1){
                    if(j!=i && bits0[j]!=bits1[j]){
                        CNOT(qs[i],qs[j]);
                        if(bits0[j]){
                            X(qs[j]);
                        }
                    }       
                }
            }else{
                set i = ii;
                H(qs[i]);
                for(j in 0..N-1){
                    if(j!=i && bits0[j]!=bits1[j]){
                        CNOT(qs[i],qs[j]);
                    }       
                }
            }

        }
    }

}