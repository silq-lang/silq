namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation add1m3(x: Qubit[]): Unit{
    body(...){
      CNOT(x[1],x[0]);
      CNOT(x[0],x[1]);
      X(x[0]);
    }
    adjoint auto;
    controlled auto;
    adjoint controlled auto;
  }
  operation add2m3(x: Qubit[]): Unit{
    body(...){
      X(x[0]);
      CNOT(x[0],x[1]);
      CNOT(x[1],x[0]);
    }
    adjoint auto;
    controlled auto;
    adjoint controlled auto;
  }
  operation Solve (x : Qubit[], y : Qubit) : Unit {
    body (...) {
      let N = Length(x);
      using(anc = Qubit[2]){
        for(i in 0..N-1){
          Controlled add1m3(x[i..i],anc);
        }
        X(anc[0]);
        X(anc[1]);
        Controlled X(anc,y);
        X(anc[0]);
        X(anc[1]);
        for(i in 0..N-1){
          Controlled add2m3(x[i..i],anc);
        }
      }
    }
    adjoint auto;
  }
}