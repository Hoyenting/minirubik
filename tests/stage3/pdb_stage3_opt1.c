#include <limits.h>

#include <stdint.h>

#include <stdio.h>

#include <stdlib.h>

#include <string.h>



static uint64_t rank_calls = 0;



enum {

    CUBIES = 7,

    PERMUTATIONS = 5040,

    ORIENTATIONS = 729,

    STATES = PERMUTATIONS * ORIENTATIONS,

    FACES = 3,

    MOVES = 9,

    MAX_SOLUTION = 32,

    FOUND = -1

};



typedef struct {

    uint8_t p[CUBIES];

    uint8_t o[CUBIES];

} state_t;



typedef struct {

    uint16_t perm[FACES][PERMUTATIONS];

    uint16_t ori[FACES][ORIENTATIONS];

} transitions_t;



typedef struct {

    unsigned long long visited;

    unsigned long long expanded;

} ida_stats_t;



static const char *const move_names[MOVES] = {

    "R", "R2", "R'", "B", "B2", "B'", "D", "D2", "D'"

};



/* Each destination takes a cubie from source[face][destination]. */

static const uint8_t source[FACES][CUBIES] = {

    {1, 4, 2, 0, 3, 5, 6},

    {0, 1, 2, 4, 5, 6, 3},

    {0, 2, 5, 3, 1, 4, 6},

};



static const uint8_t twist[FACES][CUBIES] = {

    {1, 2, 0, 2, 1, 0, 0},

    {0, 0, 0, 1, 2, 1, 2},

    {0, 0, 0, 0, 0, 0, 0},

};



static state_t quarter_turn(state_t state, uint8_t face)

{

    state_t result;

    for (uint8_t i = 0; i < CUBIES; ++i) {

        uint8_t from = source[face][i];

        result.p[i] = state.p[from];

        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);

    }

    return result;

}



static state_t apply_move(state_t state, uint8_t move)

{

    uint8_t turns = (uint8_t) (move % 3U + 1U);

    uint8_t face = (uint8_t) (move / 3U);

    for (uint8_t i = 0; i < turns; ++i)

        state = quarter_turn(state, face);

    return state;

}



static uint32_t rank_state(const state_t *state)

{

    ++rank_calls;

    uint32_t p = 0, o = 0;



    for (uint8_t i = 0; i < CUBIES; ++i) {

        uint8_t smaller = 0;

        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)

            if (state->p[j] < state->p[i])

                ++smaller;

        p = p * (CUBIES - i) + smaller;

    }



    for (uint8_t i = 0; i < 6; ++i)

        o = o * 3U + state->o[i];



    return p * ORIENTATIONS + o;

}



static void unrank_state(uint32_t rank, state_t *state)

{

    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};

    uint32_t p = rank / ORIENTATIONS;

    uint32_t o = rank % ORIENTATIONS;

    uint32_t f = 720;

    uint8_t sum = 0;



    for (uint8_t i = 0; i < CUBIES; ++i) {

        uint8_t q = (uint8_t) (p / f);

        p %= f;

        state->p[i] = available[q];



        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)

            available[j] = available[j + 1U];



        if (i < 5)

            f /= 6U - i;

    }



    for (uint8_t i = 6; i-- > 0;) {

        state->o[i] = (uint8_t) (o % 3U);

        sum = (uint8_t) (sum + state->o[i]);

        o /= 3U;

    }

    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);

}



static int valid(const state_t *state)

{

    uint8_t seen = 0;

    uint8_t sum = 0;



    for (uint8_t i = 0; i < CUBIES; ++i) {

        if (state->p[i] >= CUBIES || state->o[i] >= 3)

            return 0;

        if (seen & (uint8_t) (1U << state->p[i]))

            return 0;

        seen |= (uint8_t) (1U << state->p[i]);

        sum = (uint8_t) (sum + state->o[i]);

    }



    return sum % 3U == 0;

}



static int parse_state(const char *input, state_t *state)

{

    if (strlen(input) != 14)

        return 0;



    for (int i = 0; i < 14; ++i) {

        int limit = i < 7 ? 7 : 3;

        if (input[i] < '1' || input[i] > '0' + limit)

            return 0;

        (i < 7 ? state->p : state->o)[i % 7] =

            (uint8_t) (input[i] - '1');

    }



    return valid(state);

}



static int output_failed(void)

{

    return fflush(stdout) != 0 || ferror(stdout);

}



static int self_test(void)

{

    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};

    state_t state;



    for (uint8_t move = 0; move < MOVES; ++move) {

        state = apply_move(solved, move);

        state = apply_move(state, (uint8_t) ((move / 3U) * 3U + (2U - move % 3U)));

        if (memcmp(&solved, &state, sizeof solved) != 0)

            return 0;

    }



    for (uint32_t rank = 0; rank < STATES; ++rank) {

        unrank_state(rank, &state);

        if (!valid(&state) || rank_state(&state) != rank)

            return 0;

    }



    return 1;

}



/* Build the factored quarter-turn transition tables once. */

static void build_transitions(transitions_t *t)

{

    state_t state;



    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {

        unrank_state((uint32_t) rank * ORIENTATIONS, &state);

        for (uint8_t face = 0; face < FACES; ++face) {

            state_t next = quarter_turn(state, face);

            t->perm[face][rank] =

                (uint16_t) (rank_state(&next) / ORIENTATIONS);

        }

    }



    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {

        unrank_state(rank, &state);

        for (uint8_t face = 0; face < FACES; ++face) {

            state_t next = quarter_turn(state, face);

            t->ori[face][rank] =

                (uint16_t) (rank_state(&next) % ORIENTATIONS);

        }

    }

}



/* Exact distance in the permutation abstraction. */

static void build_perm_dist(const transitions_t *t,

                            uint8_t dist[PERMUTATIONS])

{

    uint16_t queue[PERMUTATIONS];

    uint32_t head = 0, tail = 1;



    memset(dist, UINT8_MAX, PERMUTATIONS);

    dist[0] = 0;

    queue[0] = 0;



    while (head < tail) {

        uint16_t p = queue[head++];



        for (uint8_t face = 0; face < FACES; ++face) {

            uint16_t next_p = p;

            for (uint8_t turn = 0; turn < 3; ++turn) {

                next_p = t->perm[face][next_p];

                if (dist[next_p] == UINT8_MAX) {

                    dist[next_p] = (uint8_t) (dist[p] + 1U);

                    queue[tail++] = next_p;

                }

            }

        }

    }

}



/* Exact distance in the orientation abstraction. */

static void build_ori_dist(const transitions_t *t,

                           uint8_t dist[ORIENTATIONS])

{

    uint16_t queue[ORIENTATIONS];

    uint32_t head = 0, tail = 1;



    memset(dist, UINT8_MAX, ORIENTATIONS);

    dist[0] = 0;

    queue[0] = 0;



    while (head < tail) {

        uint16_t o = queue[head++];



        for (uint8_t face = 0; face < FACES; ++face) {

            uint16_t next_o = o;

            for (uint8_t turn = 0; turn < 3; ++turn) {

                next_o = t->ori[face][next_o];

                if (dist[next_o] == UINT8_MAX) {

                    dist[next_o] = (uint8_t) (dist[o] + 1U);

                    queue[tail++] = next_o;

                }

            }

        }

    }

}



static int heuristic_from_rank(uint32_t rank,
                               const uint8_t *perm_dist,
                               const uint8_t *ori_dist)
{
    uint16_t p = (uint16_t) (rank / ORIENTATIONS);
    uint16_t o = (uint16_t) (rank % ORIENTATIONS);
    return perm_dist[p] > ori_dist[o] ? perm_dist[p] : ori_dist[o];
}

static int heuristic_bound(const state_t *state,
                           const uint8_t *perm_dist,
                           const uint8_t *ori_dist)
{
    return heuristic_from_rank(rank_state(state), perm_dist, ori_dist);
}



static int ida_dfs(state_t state, int g, int bound, int last_face,

                   int depth, const uint8_t *perm_dist,

                   const uint8_t *ori_dist,

                   uint8_t *path, uint8_t *solution, int *solution_len,

                   ida_stats_t *stats)

{

    ++stats->visited;



    uint32_t rank = rank_state(&state);

    if (rank == 0) {

        *solution_len = depth;

        memcpy(solution, path, (size_t) depth);

        return FOUND;

    }

    int f = g + heuristic_from_rank(rank, perm_dist, ori_dist);

    if (f > bound)

        return f;



    ++stats->expanded;



    int min_next = INT_MAX;

    for (uint8_t move = 0; move < MOVES; ++move) {

        int face = (int) (move / 3U);



        /* Two consecutive turns of the same face can be replaced by one move. */

        if (face == last_face)

            continue;



        path[depth] = move;

        state_t next = apply_move(state, move);



        int result = ida_dfs(next, g + 1, bound, face, depth + 1,

                             perm_dist, ori_dist,

                             path, solution, solution_len, stats);



        if (result == FOUND)

            return FOUND;

        if (result < min_next)

            min_next = result;

    }



    return min_next;

}



static int ida_solve(const state_t *start,

                     const uint8_t *perm_dist,

                     const uint8_t *ori_dist,

                     uint8_t *solution, int *solution_len,

                     ida_stats_t *stats, int verbose)

{

    uint8_t path[MAX_SOLUTION];
    uint32_t start_rank = rank_state(start);
    int bound = heuristic_from_rank(start_rank, perm_dist, ori_dist);



    stats->visited = 0;

    stats->expanded = 0;

    *solution_len = 0;



    
    if (start_rank == 0)
        return 1;



    for (;;) {

        unsigned long long visited_before = stats->visited;

        unsigned long long expanded_before = stats->expanded;



        int result = ida_dfs(*start, 0, bound, -1, 0,

                             perm_dist, ori_dist,

                             path, solution, solution_len, stats);



        if (verbose) {

            unsigned long long round_visited =

                stats->visited - visited_before;

            unsigned long long round_expanded =

                stats->expanded - expanded_before;



            printf("bound %d: visited = %llu, expanded = %llu",

                   bound, round_visited, round_expanded);



            if (result == FOUND)

                printf(" -> solved\n");

            else if (result == INT_MAX)

                printf(" -> no solution\n");

            else

                printf(" -> next bound = %d\n", result);

        }



        if (result == FOUND)

            return 1;

        if (result == INT_MAX)

            return 0;



        bound = result;

    }

}



/* Host-only exact BFS oracle used by the correctness checks. */

static uint8_t *build_exact_dist(const transitions_t *t)

{

    uint8_t *dist = malloc(STATES);

    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);

    uint32_t head = 0, tail = 1;



    if (!dist || !queue) {

        free(dist);

        free(queue);

        return NULL;

    }



    memset(dist, UINT8_MAX, STATES);

    dist[0] = 0;

    queue[0] = 0;



    while (head < tail) {

        uint32_t here = queue[head++];

        uint16_t p = (uint16_t) (here / ORIENTATIONS);

        uint16_t o = (uint16_t) (here % ORIENTATIONS);



        for (uint8_t face = 0; face < FACES; ++face) {

            uint16_t next_p = p;

            uint16_t next_o = o;



            for (uint8_t turn = 0; turn < 3; ++turn) {

                next_p = t->perm[face][next_p];

                next_o = t->ori[face][next_o];



                uint32_t there =

                    (uint32_t) next_p * ORIENTATIONS + next_o;



                if (dist[there] == UINT8_MAX) {

                    dist[there] = (uint8_t) (dist[here] + 1U);

                    queue[tail++] = there;

                }

            }

        }

    }



    free(queue);



    if (tail != STATES) {

        free(dist);

        return NULL;

    }



    return dist;

}



static int verify_h1(const uint8_t *exact_dist,

                     const uint8_t *perm_dist,

                     const uint8_t *ori_dist)

{

    uint32_t violations = 0;

    uint8_t max_h = 0;



    for (uint32_t rank = 0; rank < STATES; ++rank) {

        uint16_t p = (uint16_t) (rank / ORIENTATIONS);

        uint16_t o = (uint16_t) (rank % ORIENTATIONS);

        uint8_t h = perm_dist[p] > ori_dist[o] ? perm_dist[p] : ori_dist[o];



        if (h > max_h)

            max_h = h;



        if (h > exact_dist[rank]) {

            if (violations < 10) {

                printf("H1 violation: rank=%u h=%u exact=%u\n",

                       (unsigned) rank, (unsigned) h,

                       (unsigned) exact_dist[rank]);

            }

            ++violations;

        }

    }



    printf("H1 admissibility\n");

    printf("states checked: %u\n", (unsigned) STATES);

    printf("max heuristic: %u\n", (unsigned) max_h);

    printf("violations: %u\n", (unsigned) violations);

    printf("H1: %s\n", violations == 0 ? "PASS" : "FAIL");



    return violations == 0;

}



static int verify_h2(const uint8_t *perm_dist,

                     const uint8_t *ori_dist)

{

    uint32_t perm_visited = 0, ori_visited = 0;

    uint8_t perm_max = 0, ori_max = 0;



    for (uint32_t i = 0; i < PERMUTATIONS; ++i) {

        if (perm_dist[i] != UINT8_MAX) {

            ++perm_visited;

            if (perm_dist[i] > perm_max)

                perm_max = perm_dist[i];

        }

    }



    for (uint32_t i = 0; i < ORIENTATIONS; ++i) {

        if (ori_dist[i] != UINT8_MAX) {

            ++ori_visited;

            if (ori_dist[i] > ori_max)

                ori_max = ori_dist[i];

        }

    }



    int pass = perm_visited == PERMUTATIONS &&

               ori_visited == ORIENTATIONS &&

               perm_dist[0] == 0 && ori_dist[0] == 0;



    printf("\nH2 table completeness\n");

    printf("permutation: %u / %u, solved = %u, max = %u\n",

           (unsigned) perm_visited, (unsigned) PERMUTATIONS,

           (unsigned) perm_dist[0], (unsigned) perm_max);

    printf("orientation: %u / %u, solved = %u, max = %u\n",

           (unsigned) ori_visited, (unsigned) ORIENTATIONS,

           (unsigned) ori_dist[0], (unsigned) ori_max);

    printf("H2: %s\n", pass ? "PASS" : "FAIL");



    return pass;

}



static int verify_h3(const uint8_t *exact_dist,

                     const uint8_t *perm_dist,

                     const uint8_t *ori_dist)

{

    uint32_t mismatches = 0;

    uint32_t checked = 0;



    uint8_t solution[MAX_SOLUTION];

    int solution_len;

    ida_stats_t stats;

    state_t state;



    printf("\nH3 global optimality\n");



    for (uint32_t rank = 0; rank < STATES; ++rank) {

        unrank_state(rank, &state);



        if (!ida_solve(&state, perm_dist, ori_dist,

                       solution, &solution_len, &stats, 0)) {

            if (mismatches < 10) {

                printf("H3 failure: rank=%u no solution found\n",

                       (unsigned) rank);

            }

            ++mismatches;

        } else if (solution_len != exact_dist[rank]) {

            if (mismatches < 10) {

                printf("H3 mismatch: rank=%u ida=%d exact=%u\n",

                       (unsigned) rank,

                       solution_len,

                       (unsigned) exact_dist[rank]);

            }

            ++mismatches;

        }



        ++checked;



        /*

         * Progress output only. This is useful because H3 can take much

         * longer than H1/H2.

         */

        if (checked % 100000U == 0)

            printf("checked: %u / %u\n",

                   (unsigned) checked, (unsigned) STATES);

    }



    printf("states checked: %u\n", (unsigned) checked);

    printf("mismatches: %u\n", (unsigned) mismatches);

    printf("H3: %s\n", mismatches == 0 ? "PASS" : "FAIL");



    return mismatches == 0;

}



static int run_verify(const transitions_t *t,

                      const uint8_t *perm_dist,

                      const uint8_t *ori_dist)

{

    printf("Building exact BFS distance table...\n\n");

    uint8_t *exact_dist = build_exact_dist(t);

    if (!exact_dist) {

        fputs("failed to build exact distance table\n", stderr);

        return 0;

    }



    int h1 = verify_h1(exact_dist, perm_dist, ori_dist);

    int h2 = verify_h2(perm_dist, ori_dist);

    int h3 = verify_h3(exact_dist, perm_dist, ori_dist);



    uint8_t diameter = 0;

    for (uint32_t rank = 0; rank < STATES; ++rank)

        if (exact_dist[rank] > diameter)

            diameter = exact_dist[rank];



    printf("\nExact BFS diameter: %u\n", (unsigned) diameter);



    free(exact_dist);

    return h1 && h2 && h3 && diameter == 11;

}



static void print_solution(const uint8_t *solution, int solution_len)

{

    for (int i = 0; i < solution_len; ++i)

        printf("%s%s", i ? " " : "", move_names[solution[i]]);

    putchar('\n');

}



int main(int argc, char **argv)

{

    if (argc == 2 && !strcmp(argv[1], "--self-test")) {

        if (!self_test()) {

            fputs("self-test failed\n", stderr);

            return 1;

        }

        puts("self-test: PASS");

        return output_failed();

    }



    transitions_t transitions;

    uint8_t perm_dist[PERMUTATIONS];

    uint8_t ori_dist[ORIENTATIONS];



    build_transitions(&transitions);

    build_perm_dist(&transitions, perm_dist);

    build_ori_dist(&transitions, ori_dist);



    if (argc == 2 && !strcmp(argv[1], "--verify")) {

        int ok = run_verify(&transitions, perm_dist, ori_dist);

        return ok ? output_failed() : 1;

    }



    state_t state;

    if (argc != 2 || !parse_state(argv[1], &state)) {

        fprintf(stderr,

                "usage: %s PPPPPPPOOOOOOO\n"

                "       %s --self-test\n"

                "       %s --verify\n",

                argc > 0 && argv[0] ? argv[0] : "pdb",

                argc > 0 && argv[0] ? argv[0] : "pdb",

                argc > 0 && argv[0] ? argv[0] : "pdb");

        return 2;

    }



    uint8_t solution[MAX_SOLUTION];

    int solution_len = 0;

    ida_stats_t stats;

    int initial_bound = heuristic_bound(&state, perm_dist, ori_dist);



    
    /* Count rank_state() calls made by ida_solve/search only. */
    rank_calls = 0;

    if (!ida_solve(&state, perm_dist, ori_dist,

                   solution, &solution_len, &stats, 1)) {

        fputs("no solution found\n", stderr);

        return 1;

    }



    printf("initial heuristic bound = %d\n", initial_bound);

    printf("solution length = %d\n", solution_len);

    printf("visited nodes = %llu\n", stats.visited);

    printf("expanded nodes = %llu\n", stats.expanded);

    print_solution(solution, solution_len);

    printf("rank_state calls = %llu\n",

       (unsigned long long) rank_calls);

    return output_failed();

}
