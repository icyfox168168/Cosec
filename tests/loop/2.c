int main() {
	int j;
	for (int i = 0; i < 100; i += 1) {
		j = i;
	}
	return j; // expect: 99
}
