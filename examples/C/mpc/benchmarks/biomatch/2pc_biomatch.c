unsigned main(
    __attribute__((private(0))) unsigned db[1024],
    __attribute__((private(1))) unsigned sample[4])
{
    unsigned N = 256;
    unsigned K = 4;
    unsigned matches[N];

    // Compute distances
    for (unsigned i = 0; i < N; i++)
    {
        unsigned db_inner[K];
        for (unsigned j = 0; j < K; j++)
        {
            db_inner[j] = db[i * K + j];
        }

        unsigned r = 0;
        for (unsigned k = 0; k < K; k++)
        {
            unsigned t = (db_inner[k] - sample[k]);
            r += t * t;
        }
        matches[i] = r;
    }

    // Compute minimum
    unsigned best_match = matches[0];
    for (unsigned l = 1; l < N; l++)
    {
        if (matches[l] < best_match)
        {
            best_match = matches[l];
        }
    }

    return best_match;
}