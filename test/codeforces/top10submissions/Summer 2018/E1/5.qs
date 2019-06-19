namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
        
            mutable v = new Int[N];
            
            using(qubits = Qubit[N + 1]){
                let qs = qubits[0..(N - 1)];
                let ancilla = qubits[N];
                
                X(ancilla);
                H(ancilla);
                
                for(i in 0..(N - 1)){
                    H(qs[i]);
                }
                
                Uf(qs, ancilla);
                
                for(i in 0..(N - 1)){
                    H(qs[i]);
                }
                
                for(i in 0..(N - 1)){
                    if(M(qs[i]) == One){
                        set v[i] = 1;
                    }
                    else{
                        set v[i] = 0;
                    }
                }
                
                ResetAll(qubits);
            }
            
            return(v);
        }
    }
}