namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let N = Length(x);
            for(i in 1..(N-1)){
              CNOT(x[i],x[i-1]);
              //1 if alternating, 0 if not, now in i-1
            }
            Controlled X(x[0..N-2],y);
            for(i in (N-1)..-1..1){
              CNOT(x[i],x[i-1]);
            }
        }
      adjoint auto;
  }
}