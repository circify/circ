int main(__attribute__((private(0))) int a[20], __attribute__((private(1))) int b[20])
{
    int D = 2;
    int NA = 10;
    int NB = 10;
    int NC = 5;
    int PRECISION = 4;
    int LEN = NA + NB;
    int LEN_OUTER = 10;
    int LEN_INNER = LEN / LEN_OUTER;

    // init data
    int data[LEN * D];
    for (int i_0 = 0; i_0 < D * NA; i_0++)
    {
        data[i_0] = a[i_0];
    }
    int offset = D * NA;
    for (int i_1 = 0; i_1 < D * NB; i_1++)
    {
        data[i_1 + offset] = b[i_1];
    }

    int output[D * NC];

    // ======================= kmeans
    int cluster[D * NC];

    // Assign random start cluster from data
    for (int i_2 = 0; i_2 < NC; i_2++)
    {
        cluster[i_2 * D] = data[((i_2 + 3) % LEN) * D];
        cluster[i_2 * D + 1] = data[((i_2 + 3) % LEN) * D + 1];
    }

    for (int i_3 = 0; i_3 < PRECISION; i_3++)
    {
        int new_cluster[D * NC];

        // ======================= iteration_unrolled_outer
        int count[NC];

        // Set Outer result
        for (int i_4 = 0; i_4 < NC; i_4++)
        {
            new_cluster[i_4 * D] = 0;
            new_cluster[i_4 * D + 1] = 0;
            count[i_4] = 0;
        }

        int loop_clusterD1[NC * LEN_OUTER];
        int loop_clusterD2[NC * LEN_OUTER];
        int loop_count[NC * LEN_OUTER];

        // Compute decomposition
        for (int i_5 = 0; i_5 < LEN_OUTER; i_5++)
        {
            // Copy data, fasthack for scalability
            int data_offset = i_5 * LEN_INNER * D;
            int data_inner[LEN_INNER * D];

            // memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(coord_t));
            for (int i_6 = 0; i_6 < LEN_INNER * D; i_6++)
            {
                data_inner[i_6] = data[i_6 + data_offset];
            }

            int cluster_inner[NC * D];
            int count_inner[NC];

            // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);
            int dist[NC];
            int pos[NC];
            int bestMap_inner[LEN_INNER];

            for (int i_7 = 0; i_7 < NC; i_7++)
            {
                cluster_inner[i_7 * D] = 0;
                cluster_inner[i_7 * D + 1] = 0;
                count_inner[i_7] = 0;
            }

            // Compute nearest clusters for Data item i
            for (int i_8 = 0; i_8 < LEN_INNER; i_8++)
            {
                int dx = data_inner[i_8 * D];
                int dy = data_inner[i_8 * D + 1];

                for (int i_9 = 0; i_9 < NC; i_9++)
                {
                    pos[i_9] = i_9;
                    int x1 = cluster[D * i_9];
                    int y1 = cluster[D * i_9 + 1];
                    int x2 = dx;
                    int y2 = dy;
                    dist[i_9] = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2);
                }
                // hardcoded NC = 5;
                // stride = 1
                // stride = 2
                // stride = 4
                int stride = 1;
                for (int i_10 = 0; i_10 < NC - stride; i_10 += 2)
                {
                    if (dist[i_10 + stride] < dist[i_10])
                    {
                        dist[i_10] = dist[i_10 + stride];
                        pos[i_10] = pos[i_10 + stride];
                    }
                }
                stride = 2;
                for (int i_11 = 0; i_11 < NC - stride; i_11 += 4)
                {
                    if (dist[i_11 + stride] < dist[i_11])
                    {
                        dist[i_11] = dist[i_11 + stride];
                        pos[i_11] = pos[i_11 + stride];
                    }
                }
                stride = 4;
                for (int i_12 = 0; i_12 < NC - stride; i_12 += 8)
                {
                    if (dist[i_12 + stride] < dist[i_12])
                    {
                        dist[i_12] = dist[i_12 + stride];
                        pos[i_12] = pos[i_12 + stride];
                    }
                }
                bestMap_inner[i_8] = pos[0];
                int cc = bestMap_inner[i_8];
                cluster_inner[cc * D] += data_inner[i_8 * D];
                cluster_inner[cc * D + 1] += data_inner[i_8 * D + 1];
                count_inner[cc] += 1;
            }
            // // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);

            for (int i_13 = 0; i_13 < NC; i_13++)
            {
                loop_clusterD1[i_13 * LEN_OUTER + i_5] = cluster_inner[i_13 * D];
                loop_clusterD2[i_13 * LEN_OUTER + i_5] = cluster_inner[i_13 * D + 1];
                loop_count[i_13 * LEN_OUTER + i_5] = count_inner[i_13];
            }
        }

        for (int i_14 = 0; i_14 < NC; i_14++)
        {
            new_cluster[i_14 * D] =
                loop_clusterD1[i_14 * LEN_OUTER + 0] + loop_clusterD1[i_14 * LEN_OUTER + 1] +
                loop_clusterD1[i_14 * LEN_OUTER + 2] + loop_clusterD1[i_14 * LEN_OUTER + 3] +
                loop_clusterD1[i_14 * LEN_OUTER + 4] + loop_clusterD1[i_14 * LEN_OUTER + 5] +
                loop_clusterD1[i_14 * LEN_OUTER + 6] + loop_clusterD1[i_14 * LEN_OUTER + 7] +
                loop_clusterD1[i_14 * LEN_OUTER + 8] + loop_clusterD1[i_14 * LEN_OUTER + 9];

            new_cluster[i_14 * D + 1] =
                loop_clusterD2[i_14 * LEN_OUTER + 0] + loop_clusterD2[i_14 * LEN_OUTER + 1] +
                loop_clusterD2[i_14 * LEN_OUTER + 2] + loop_clusterD2[i_14 * LEN_OUTER + 3] +
                loop_clusterD2[i_14 * LEN_OUTER + 4] + loop_clusterD2[i_14 * LEN_OUTER + 5] +
                loop_clusterD2[i_14 * LEN_OUTER + 6] + loop_clusterD2[i_14 * LEN_OUTER + 7] +
                loop_clusterD2[i_14 * LEN_OUTER + 8] + loop_clusterD2[i_14 * LEN_OUTER + 9];

            count[i_14] =
                loop_count[i_14 * LEN_OUTER + 0] + loop_count[i_14 * LEN_OUTER + 1] +
                loop_count[i_14 * LEN_OUTER + 2] + loop_count[i_14 * LEN_OUTER + 3] +
                loop_count[i_14 * LEN_OUTER + 4] + loop_count[i_14 * LEN_OUTER + 5] +
                loop_count[i_14 * LEN_OUTER + 6] + loop_count[i_14 * LEN_OUTER + 7] +
                loop_count[i_14 * LEN_OUTER + 8] + loop_count[i_14 * LEN_OUTER + 9];
        }

        // Recompute cluster Pos
        // Compute mean
        for (int i_15 = 0; i_15 < NC; i_15++)
        {
            if (count[i_15] > 0)
            {
                new_cluster[i_15 * D] /= count[i_15];
                new_cluster[i_15 * D + 1] /= count[i_15];
            }
        }
        // ======================= iteration_unrolled_outer

        // We need to copy inputs to outputs
        for (int i_16 = 0; i_16 < NC * D; i_16++)
        {
            cluster[i_16] = new_cluster[i_16];
        }
    }
    for (int i_17 = 0; i_17 < NC; i_17++)
    {
        output[i_17 * D] = cluster[i_17 * D];
        output[i_17 * D + 1] = cluster[i_17 * D + 1];
    }
    // ======================= kmeans
    // return output[0];

    int sum = 0;
    for (int i_18 = 0; i_18 < D * NC; i_18++)
    {
        sum += output[i_18];
    }

    return sum;
}
