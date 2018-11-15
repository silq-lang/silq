// compilation errors

def main(const n: int[32],b:!ℤ)lifted:int[32]×int[32]×int[32]{
	y₁ := main: const !int[32]×!𝔹 →lifted 𝟙;
	y₂ := main: Π(const n: int[32],x: !𝔹) lifted. 𝟙;
	y₃ := main: const int[32] × !𝔹 →mfree 𝟙;
	m := dup(n): int[32];
	def foo(f: !(𝔹 → 𝔹)){
		return f: (𝔹 → 𝔹);
	}
	return (y₁,y₂,y₃);
}
