def main(const n: Int[32],b:!ℤ)lifted:𝟙{
	y₁ := main: const !Int[32]×!𝔹 →lifted 𝟙;
	y₂ := main: Π(const n: Int[32],x: !𝔹). lifted 𝟙;
	y₃ := main: const Int[32] × !𝔹 →mfree 𝟙;
	m := n: Int[32];
	def foo(f: !(𝔹 → 𝔹)){
		return f: (𝔹 → 𝔹);
	}
}
