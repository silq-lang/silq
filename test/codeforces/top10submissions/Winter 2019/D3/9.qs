namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation Solve (x : Qubit[]) : Unit {
    let N = Length(x);
    Controlled (ApplyToEachCA(X,_)) (x[0..0],x[1..N-1]);
    H(x[0]);
    Controlled (ApplyToEachCA(X,_)) (x[0..0],x[1..N-1]);
  }
}