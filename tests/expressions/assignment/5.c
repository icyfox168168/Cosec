int main() {
	int a = 3;
	int b = (a = 4, a);
	return b; // expect: 4
}
