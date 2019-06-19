namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Math;
  operation isPV( x: Qubit[], y: Qubit, p: Int) : Unit {
    body(...){
      let N = Length(x);
      for(i in p..N-1){
        CNOT(x[i],x[i-p]);
        //X(x[i-p]);
      }
      ApplyToEachA(X,x[0..N-p-1]);
      Controlled X(x[0..N-p-1],y);
      ApplyToEachA(X,x[0..N-p-1]);
      for(i in ((N-1)..-1..p)){
        CNOT(x[i],x[i-p]);
      }
    }
    adjoint auto;
  }
  operation IsP ( x: Qubit[], y: Qubit[]) : Unit {
    body(...){
      let N = Length(x);
      for (i in 1..N-1){
        isPV(x,y[i-1],i);
      }
      ApplyToEachA(X,y);
    }adjoint auto;
  }
  operation Solve (x : Qubit[], y : Qubit) : Unit {
    body (...) {
      let N = Length(x);
      using (anc = Qubit[N-1]) {
        WithA(IsP(x, _), Controlled X(_, y), anc);
        X(y);
        //ResetAll(anc);
      }
    }
    adjoint auto;
  }
}