int main(
    __attribute__((private(0))) int db[1024],
    __attribute__((private(1))) int sample[4])
{
    int N = 256;
    int K = 4;
    int matches[N];

    // Compute distances
    for (int i = 0; i < N; i++)
    {
        int db_inner[K];
        for (int j = 0; j < K; j++)
        {
            db_inner[j] = db[i * K + j];
        }

        int r = 0;
        for (int k = 0; k < K; k++)
        {
            int t = (db_inner[k] - sample[k]);
            r += t * t;
        }
        matches[i] = r;
    }

    // Compute minimum
    int best_match = matches[0];
    for (int l = 1; l < N; l++)
    {
        if (matches[l] < best_match)
        {
            best_match = matches[l];
        }
    }

    return best_match;
}