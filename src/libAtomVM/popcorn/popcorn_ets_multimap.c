/*
 * This file is part of AtomVM.
 *
 * Copyright 2024 Fred Dushin <fred@dushin.net>
 * Copyright 2025 Mateusz Furga <mateusz.furga@swmansion.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

#include <stdlib.h>
#include <string.h>

#include "popcorn_ets_multimap.h"
#include "popcorn_ets_multimap_hash.h"
#include "smp.h"
#include "term.h"
#include "utils.h"

static term node_key(struct EtsMultimap *multimap, struct EtsMultimapNode *node) {
    struct EtsMultimapEntry *entry = node->entries;
    return entry != NULL ? term_get_tuple_element(entry->tuple, multimap->keypos) : term_nil();
}

static struct EtsMultimapNode *ets_multimap_node_new(struct EtsMultimapNode *next, struct EtsMultimapEntry *entries) {
    struct EtsMultimapNode *node = malloc(sizeof(struct EtsMultimapNode));
    if (IS_NULL_PTR(node)) {
        return NULL;
    }

    node->next = next;
    node->entries = entries;

    return node;
}

static void ets_multimap_node_destroy(struct EtsMultimapNode *node, GlobalContext *global) {
    struct EtsMultimapEntry *entry = node->entries;

    while (entry != NULL) {
        struct EtsMultimapEntry *next = entry->next;
        memory_destroy_heap(entry->heap, global);
        free(entry);
        entry = next;
    }

    free(node);
}

struct EtsMultimap *ets_multimap_new(EtsMultimapType type, size_t keypos) {
    struct EtsMultimap *multimap = malloc(sizeof(struct EtsMultimap));
    if (IS_NULL_PTR(multimap)) {
        return NULL;
    }

    multimap->type = type;
    multimap->keypos = keypos;
    for (size_t i = 0; i < NUM_BUCKETS; i++) {
        multimap->buckets[i] = NULL;
    }

    return multimap;
}

void ets_multimap_destroy(struct EtsMultimap *multimap, GlobalContext *global) {
    for (size_t i = 0; i < NUM_BUCKETS; i++) {
        struct EtsMultimapNode *node = multimap->buckets[i];
        while (node != NULL) {
            struct EtsMultimapNode *next = node->next;
            ets_multimap_node_destroy(node, global);
            node = next;
        }
    }
}

static struct EtsMultimapEntry *ets_multimap_entry_new(term tuple) {
    struct EtsMultimapEntry *entry = malloc(sizeof(struct EtsMultimapEntry));
    if (IS_NULL_PTR(entry)) {
        return NULL;
    }

    Heap *heap = malloc(sizeof(Heap));
    if (IS_NULL_PTR(heap)) {
        free(entry);
        return NULL;
    }

    size_t size = memory_estimate_usage(tuple);  // TODO: check me
    if (UNLIKELY(memory_init_heap(heap, size) != MEMORY_GC_OK)) {
        free(entry);
        free(heap);
        return NULL;
    }

    tuple = memory_copy_term_tree(heap, tuple);

    entry->tuple = tuple;
    entry->heap = heap;
    entry->next = NULL;

    return entry;
}

void ets_multimap_entry_destroy(struct EtsMultimapEntry *entry, GlobalContext *global) {
    // TODO
}

static EtsMultimapStatus find_node(
    struct EtsMultimap *multimap,
    term key,
    struct EtsMultimapNode **out_node,  /* out */
    GlobalContext *global
) {
    uint32_t idx = hash_term(key, global) % NUM_BUCKETS;
    struct EtsMultimapNode *node = multimap->buckets[idx];

    if (IS_NULL_PTR(node)) {
        *out_node = NULL;
        return EtsMultimapOk;
    }

    while (!IS_NULL_PTR(node)) {
        TermCompareResult res = term_compare(key, node_key(multimap, node), TermCompareExact, global);

        if (res == TermCompareMemoryAllocFail) {
            return EtsMultimapError;
        }

        if (res == TermEquals) {
            *out_node = node;
            return EtsMultimapOk;
        }

        node = node->next;
    }

    *out_node = NULL;
    return EtsMultimapOk;
}

static void ets_multimap_insert_revert(
    struct EtsMultimap *multimap,
    struct EtsMultimapEntry **entries,
    size_t count,
    GlobalContext *global
) {
    for (size_t idx = 0; idx < NUM_BUCKETS; idx++) {
        struct EtsMultimapNode *node = multimap->buckets[idx];

        while (node != NULL) {
            struct EtsMultimapNode *next_node = node->next;
            struct EtsMultimapEntry *entry = node->entries;

            assert(entry != NULL);

            while (entry != NULL) {
                struct EtsMultimapEntry *next_entry = entry->next;

                for (size_t j = 0; j < count; j++) {
                    if (entry == entries[j]) {
                        node->entries = next_entry;
                    }
                }

                entry = next_entry;
            }

            if (IS_NULL_PTR(node->entries)) {
                multimap->buckets[idx] = next_node;
                ets_multimap_node_destroy(node, global);
            }

            node = next_node;
        }
    }

    for (size_t i = 0; i < count; i++) {
        ets_multimap_entry_destroy(entries[i], global);
    }
}

EtsMultimapStatus ets_multimap_insert(
    struct EtsMultimap *multimap,
    term *tuples,
    size_t count,
    GlobalContext *global
) {
    if (tuples == NULL || count == 0) {
        return EtsMultimapOk;
    }

    struct EtsMultimapEntry **entries = malloc(sizeof(struct EtsMultimapEntry *) * count);
    if (IS_NULL_PTR(entries)) {
        return EtsMultimapError;
    }

    for (size_t i = 0; i < count; i++) {
        entries[i] = ets_multimap_entry_new(tuples[i]);
        if (IS_NULL_PTR(entries[i])) {
            for (size_t j = 0; j < i; j++) {
                ets_multimap_entry_destroy(entries[j], global);
            }
            free(entries);
            return EtsMultimapError;
        }
    }

    EtsMultimapStatus status = EtsMultimapOk;
    bool error = false;

    for (size_t i = 0; i < count; i++) {
        struct EtsMultimapEntry *entry = entries[i];
        term key = term_get_tuple_element(entry->tuple, multimap->keypos);

        struct EtsMultimapNode *node;
        if (find_node(multimap, key, &node, global) == EtsMultimapError) {
            error = true;
            status = EtsMultimapError;
            break;
        }

        if (IS_NULL_PTR(node)) {
            uint32_t idx = hash_term(key, global) % NUM_BUCKETS;
            struct EtsMultimapNode *new_node = ets_multimap_node_new(NULL, entry);
            if (IS_NULL_PTR(new_node)) {
                error = true;
                status = EtsMultimapError;
                break;
            }

            assert(new_node->entries != NULL);

            new_node->next = multimap->buckets[idx];
            multimap->buckets[idx] = new_node;
            continue;
        }

        assert(node->entries != NULL);

        entry->next = node->entries;
        node->entries = entry;
    }

    if (error) {
        ets_multimap_insert_revert(multimap, entries, count, global);
    }

    free(entries);

    return status;
}

EtsMultimapStatus ets_multimap_lookup(
    struct EtsMultimap *multimap,
    term key,
    term **tuples,
    size_t *count,
    GlobalContext *global
) {
    if (count == NULL) {
        return EtsMultimapError;
    }
    *count = 0;

    EtsMultimapStatus result;

    struct EtsMultimapNode *node;
    if ((result = find_node(multimap, key, &node, global)) != EtsMultimapOk) {
        return result;
    }

    if (IS_NULL_PTR(node)) {
        return EtsMultimapOk;
    }

    assert(node != NULL);
    assert(node->entries != NULL);

    for (struct EtsMultimapEntry *iter = node->entries; iter != NULL; iter = iter->next) {
        (*count)++;
    }

    if (tuples == NULL) {
        /* only return number of tuples found */
        return EtsMultimapOk;
    }

    *tuples = malloc(sizeof(term) * (*count));
    if (IS_NULL_PTR(*tuples)) {
        return EtsMultimapError;
    }

    size_t i = 0;
    for (struct EtsMultimapEntry *iter = node->entries; iter != NULL; iter = iter->next, i++) {
        assert(i < *count);
        (*tuples)[i] = iter->tuple;
    }

    return EtsMultimapOk;
}

bool ets_multimap_remove(
    struct EtsMultimap *multimap,
    term key,
    GlobalContext *global
) {
    return false;
}
