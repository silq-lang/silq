namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation a1 (x : Qubit[]) : Unit {
    body(...) {
      if(Length(x)>1){
        Controlled a1(x[0..0],x[1..Length(x)-1]);
      }
      X(x[0]);
    }controlled auto;
  }
  operation xWing(x: Qubit[]): Unit{
    let N = Length(x);
    Controlled (ApplyToEachCA(X,_)) (x[0..0],x[1..N-1]);
    H(x[0]);
    Controlled (ApplyToEachCA(X,_)) (x[0..0],x[1..N-1]);
  }
  operation Solve (x : Qubit[]) : Unit {
    let N = Length(x);
    Controlled (ApplyToEachCA(X,_)) (x[N-1..N-1],x[0..N-2]);
    X(x[N-1]);
    Controlled a1(x[N-1..N-1],x[0..N-2]);
    X(x[N-1]);
    Controlled a1(x[N-1..N-1],x[0..N-2]);
    Controlled (ApplyToEachCA(X,_)) (x[N-1..N-1],x[0..N-2]);
    X(x[N-1]);
    xWing(x);
  }
}