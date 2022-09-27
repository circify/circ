unsigned main(__attribute__((private(0))) unsigned a[20], __attribute__((private(1))) unsigned b[20])
{
    unsigned D = 2;
    unsigned NA = 10;
    unsigned NB = 10;
    unsigned NC = 5;
    unsigned PRECISION = 4;
    unsigned LEN = NA + NB;
    unsigned LEN_OUTER = 10;
    unsigned LEN_INNER = LEN / LEN_OUTER;

    // init data
    unsigned data[LEN * D];
    for (unsigned i_0 = 0; i_0 < D * NA; i_0++)
    {
        data[i_0] = a[i_0];
    }
    unsigned offset = D * NA;
    for (unsigned i_1 = 0; i_1 < D * NB; i_1++)
    {
        data[i_1 + offset] = b[i_1];
    }

    unsigned output[D * NC];

    // ======================= kmeans
    unsigned cluster[D * NC];

    // Assign random start cluster from data
    for (unsigned i_2 = 0; i_2 < NC; i_2++)
    {
        cluster[i_2 * D] = data[((i_2 + 3) % LEN) * D];
        cluster[i_2 * D + 1] = data[((i_2 + 3) % LEN) * D + 1];
    }

    for (unsigned i_3 = 0; i_3 < PRECISION; i_3++)
    {
        unsigned new_cluster[D * NC];

        // ======================= iteration_unrolled_outer
        unsigned count[NC];

        // Set Outer result
        for (unsigned i_4 = 0; i_4 < NC; i_4++)
        {
            new_cluster[i_4 * D] = 0;
            new_cluster[i_4 * D + 1] = 0;
            count[i_4] = 0;
        }

        unsigned loop_clusterD1[NC * LEN_OUTER];
        unsigned loop_clusterD2[NC * LEN_OUTER];
        unsigned loop_count[NC * LEN_OUTER];

        // Compute decomposition
        for (unsigned i_5 = 0; i_5 < LEN_OUTER; i_5++)
        {
            // Copy data, fasthack for scalability
            unsigned data_offset = i_5 * LEN_INNER * D;
            unsigned data_inner[LEN_INNER * D];

            // memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(coord_t));
            for (unsigned i_6 = 0; i_6 < LEN_INNER * D; i_6++)
            {
                data_inner[i_6] = data[i_6 + data_offset];
            }

            unsigned cluster_inner[NC * D];
            unsigned count_inner[NC];

            // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);
            unsigned dist[NC];
            unsigned pos[NC];
            unsigned bestMap_inner[LEN_INNER];

            for (unsigned i_7 = 0; i_7 < NC; i_7++)
            {
                cluster_inner[i_7 * D] = 0;
                cluster_inner[i_7 * D + 1] = 0;
                count_inner[i_7] = 0;
            }

            // Compute nearest clusters for Data item i
            for (unsigned i_8 = 0; i_8 < LEN_INNER; i_8++)
            {
                unsigned dx = data_inner[i_8 * D];
                unsigned dy = data_inner[i_8 * D + 1];

                for (unsigned i_9 = 0; i_9 < NC; i_9++)
                {
                    pos[i_9] = i_9;
                    unsigned x1 = cluster[D * i_9];
                    unsigned y1 = cluster[D * i_9 + 1];
                    unsigned x2 = dx;
                    unsigned y2 = dy;
                    dist[i_9] = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2);
                }
                // hardcoded NC = 5;
                // stride = 1
                // stride = 2
                // stride = 4
                unsigned stride = 1;
                for (unsigned i_10 = 0; i_10 < NC - stride; i_10 += 2)
                {
                    if (dist[i_10 + stride] < dist[i_10])
                    {
                        dist[i_10] = dist[i_10 + stride];
                        pos[i_10] = pos[i_10 + stride];
                    }
                }
                stride = 2u;
                for (unsigned i_11 = 0; i_11 < NC - stride; i_11 += 4)
                {
                    if (dist[i_11 + stride] < dist[i_11])
                    {
                        dist[i_11] = dist[i_11 + stride];
                        pos[i_11] = pos[i_11 + stride];
                    }
                }
                stride = 4u;
                for (unsigned i_12 = 0; i_12 < NC - stride; i_12 += 8)
                {
                    if (dist[i_12 + stride] < dist[i_12])
                    {
                        dist[i_12] = dist[i_12 + stride];
                        pos[i_12] = pos[i_12 + stride];
                    }
                }
                bestMap_inner[i_8] = pos[0];
                unsigned cc = bestMap_inner[i_8];
                cluster_inner[cc * D] += data_inner[i_8 * D];
                cluster_inner[cc * D + 1] += data_inner[i_8 * D + 1];
                count_inner[cc] += 1;
            }
            // // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);

            for (unsigned i_13 = 0; i_13 < NC; i_13++)
            {
                loop_clusterD1[i_13 * LEN_OUTER + i_5] = cluster_inner[i_13 * D];
                loop_clusterD2[i_13 * LEN_OUTER + i_5] = cluster_inner[i_13 * D + 1];
                loop_count[i_13 * LEN_OUTER + i_5] = count_inner[i_13];
            }
        }

        for (unsigned i_14 = 0; i_14 < NC; i_14++)
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
        for (unsigned i_15 = 0; i_15 < NC; i_15++)
        {
            if (count[i_15] > 0)
            {
                new_cluster[i_15 * D] /= count[i_15];
                new_cluster[i_15 * D + 1] /= count[i_15];
            }
        }
        // ======================= iteration_unrolled_outer

        // We need to copy inputs to outputs
        for (unsigned i_16 = 0; i_16 < NC * D; i_16++)
        {
            cluster[i_16] = new_cluster[i_16];
        }
    }

    for (unsigned i_17 = 0; i_17 < NC; i_17++)
    {
        output[i_17 * D] = cluster[i_17 * D];
        output[i_17 * D + 1] = cluster[i_17 * D + 1];
    }
    // ======================= kmeans
    // return output[0];

    unsigned sum = 0;
    for (unsigned i_18 = 0; i_18 < D * NC; i_18++)
    {
        sum += output[i_18];
    }

    return sum;
}
