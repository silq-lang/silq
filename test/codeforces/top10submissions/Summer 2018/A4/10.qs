
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Helper (qs: Qubit[]) : ()
    {
        body
        {
            let N = Length(qs)/2;
            // X(qs[0]);
            H(qs[0]);
            for(i in 1..N*2-1){
                CNOT(qs[0],qs[i]);
            }   
            for(i in N..N*2-1){
                X(qs[i]);   
            }   
        }
        controlled auto;
    }

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            let N = Length(qs);
            if(N==1){
                X(qs[0]);
            }else{
            mutable n = N/2;
            Helper(qs);
            
            for(i in 0..10){
                if(n>=2){
                    for(j in 0..n..N-n){
                        if(j>0){
                            for(k in 0..n-1){
                                SWAP(qs[k],qs[j+k]);
                            }
                        }   
                        (Controlled(Helper))(qs[n..N-1],qs[0..n-1]);
                        if(j>0){
                            for(k in 0..n-1){
                                SWAP(qs[k],qs[j+k]);
                            }
                        }   
                    }
                    set n = n/2;
                }
            }
            ApplyToEach(X,qs);
            }
        }
    }

}