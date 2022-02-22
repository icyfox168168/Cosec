int main() {
	int a = 1;
	int b = 0;
	b |= a;
	return b; // expect: 1
}
