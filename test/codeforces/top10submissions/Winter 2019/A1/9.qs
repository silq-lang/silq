namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Math;
  operation Solve (qs : Qubit[]) : Unit {
      let alpha = ArcCos(Sqrt(1.0/3.0));
      //X(qs[0]);
      Ry(2.0*alpha,qs[1]);
      (Controlled H) (qs[1..1],qs[0]);
      CNOT(qs[0],qs[1]);
  }
}