library(tidyverse)
d <- read_csv("data.csv")
with_norm_cost <- d %>% 
  left_join(d %>%
              filter(name == "gcd_uniq") %>%
              mutate(norm_cost = cost) %>%
              select(log2_accesses, addr_bits, norm_cost) %>%
              mutate(),
            by=c("log2_accesses", "addr_bits")) %>%
  mutate(norm_cost = cost / norm_cost)
with_norm_cost %>%
  filter(name != "sort") %>%
  ggplot(aes(x = addr_bits, y = norm_cost, color = name)) +
  geom_point() +
  geom_line() +
  facet_wrap(vars(log2_accesses), scales = "free", labeller = label_both)
d %>%
  filter(name == "subbitsplit") %>%
  ggplot(aes(x = addr_bits, y = k)) +
  geom_point() +
  geom_line() +
  facet_wrap(vars(log2_accesses), scales = "free", labeller = label_both)
