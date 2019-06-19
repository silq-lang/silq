namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation XOR (x: Qubit[], k: Bool[]): Unit{
    let N = Length(x);
    for(i in 0..N-1){
      if(k[i]){
        X(x[i]);
      }
    }
  }
  operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
    let N = Length(qs);
    using( d = Qubit[2]){
      H(d[0]);
      H(d[1]);
      for(i in 0..(N-1)){
        if(bits[3][i]){
          Controlled X(d,qs[i]);
        }
      }
      X(d[0]);
      for(i in 0..(N-1)){
        if(bits[2][i]){
          Controlled X(d,qs[i]);
        }
      }
      X(d[1]);
      for(i in 0..(N-1)){
        if(bits[1][i]){
          Controlled X(d,qs[i]);
        }
      }
      X(d[0]);
      for(i in 0..(N-1)){
        if(bits[0][i]){
          Controlled X(d,qs[i]);
        }
      }
      X(d[1]);
      X(d[0]);
      XOR(qs,bits[1]);
      ApplyToEach(X,qs);
      Controlled X(qs,d[0]);
      XOR(qs,bits[1]);
      ApplyToEach(X,qs);
      //10
      XOR(qs,bits[2]);
      ApplyToEach(X,qs);
      Controlled X(qs,d[1]);
      Controlled X(qs,d[0]);
      XOR(qs,bits[2]);
      ApplyToEach(X,qs);
      //11
      XOR(qs,bits[3]);
      ApplyToEach(X,qs);
      Controlled X(qs,d[1]);
      //Controlled X(qs,d[0]);
      XOR(qs,bits[3]);
      ApplyToEach(X,qs);
      //Message(ToStringI(MeasureInteger(LittleEndian(d))));
      //ResetAll(d);
    }
  }
}