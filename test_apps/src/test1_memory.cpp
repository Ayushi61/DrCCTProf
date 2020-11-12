int N = 100000;

int main() {
    int A[N];
    for (int i = 0; i < N; i++) 
        A[i] = 0; // dead store
    for (int i = 0; i < N; i++) 
        A[i] = 1; // killing store
    for (int i = 0; i < N; i++) 
        A[i]++;
    return 0;
}
