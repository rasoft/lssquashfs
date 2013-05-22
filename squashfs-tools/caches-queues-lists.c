/*
 * Create a squashfs filesystem.  This is a highly compressed read only
 * filesystem.
 *
 * Copyright (c) 2013
 * Phillip Lougher <phillip@squashfs.org.uk>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2,
 * or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * caches-queues-lists.c
 */

#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "error.h"
#include "caches-queues-lists.h"

extern int add_overflow(int, int);
extern int multiply_overflow(int, int);

#define TRUE 1
#define FALSE 0

struct queue *queue_init(int size)
{
	struct queue *queue = malloc(sizeof(struct queue));

	if(queue == NULL)
		MEM_ERROR();

	if(add_overflow(size, 1) ||
				multiply_overflow(size + 1, sizeof(void *)))
		BAD_ERROR("Size too large in queue_init\n");

	queue->data = malloc(sizeof(void *) * (size + 1));
	if(queue->data == NULL)
		MEM_ERROR();

	queue->size = size + 1;
	queue->readp = queue->writep = 0;
	pthread_mutex_init(&queue->mutex, NULL);
	pthread_cond_init(&queue->empty, NULL);
	pthread_cond_init(&queue->full, NULL);

	return queue;
}


void queue_put(struct queue *queue, void *data)
{
	int nextp;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	while((nextp = (queue->writep + 1) % queue->size) == queue->readp)
		pthread_cond_wait(&queue->full, &queue->mutex);

	queue->data[queue->writep] = data;
	queue->writep = nextp;
	pthread_cond_signal(&queue->empty);
	pthread_cleanup_pop(1);
}


void *queue_get(struct queue *queue)
{
	void *data;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	while(queue->readp == queue->writep)
		pthread_cond_wait(&queue->empty, &queue->mutex);

	data = queue->data[queue->readp];
	queue->readp = (queue->readp + 1) % queue->size;
	pthread_cond_signal(&queue->full);
	pthread_cleanup_pop(1);

	return data;
}


void dump_queue(struct queue *queue)
{
	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	printf("Max size %d, size %d%s\n", queue->size - 1,  
		queue->readp <= queue->writep ? queue->writep - queue->readp :
			queue->size - queue->readp + queue->writep,
		queue->readp == queue->writep ? " (EMPTY)" :
			((queue->writep + 1) % queue->size) == queue->readp ?
			" (FULL)" : "");

	pthread_cleanup_pop(1);
}


/* define seq queue hash tables */
#define CALCULATE_SEQ_HASH(N) ((N) & 0xffff)

/* Called with the seq queue mutex held */
INSERT_HASH_TABLE(seq, struct seq_queue, CALCULATE_SEQ_HASH, sequence, seq)

/* Called with the cache mutex held */
REMOVE_HASH_TABLE(seq, struct seq_queue, CALCULATE_SEQ_HASH, sequence, seq);

static unsigned int sequence = 0;


struct seq_queue *seq_queue_init()
{
	struct seq_queue *queue = malloc(sizeof(struct seq_queue));
	if(queue == NULL)
		MEM_ERROR();

	memset(queue, 0, sizeof(struct seq_queue));

	pthread_mutex_init(&queue->mutex, NULL);
	pthread_cond_init(&queue->wait, NULL);

	return queue;
}


void seq_queue_put(struct seq_queue *queue, struct file_buffer *entry)
{
	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	insert_seq_hash_table(queue, entry);

	if(entry->fragment)
		queue->fragment_count ++;
	else
		queue->block_count ++;

	if(entry->sequence == sequence)
		pthread_cond_signal(&queue->wait);

	pthread_cleanup_pop(1);
}


struct file_buffer *seq_queue_get(struct seq_queue *queue)
{
	/*
	 * Look-up buffer matching sequence in the queue, if found return
	 * it, otherwise wait until it arrives
	 */
	int hash = CALCULATE_SEQ_HASH(sequence);
	struct file_buffer *entry;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	while(1) {
		for(entry = queue->hash_table[hash]; entry;
						entry = entry->hash_next)
			if(entry->sequence == sequence)
				break;

		if(entry) {
			/*
			 * found the buffer in the queue, decrement the
			 * appropriate count, and remove from hash list
			 */
			if(entry->fragment)
				queue->fragment_count --;
			else
				queue->block_count --;

			remove_seq_hash_table(queue, entry);

			sequence ++;

			break;
		}

		/* entry not found, wait for it to arrive */	
		pthread_cond_wait(&queue->wait, &queue->mutex);
	}

	pthread_cleanup_pop(1);

	return entry;
}


void dump_seq_queue(struct seq_queue *queue, int fragment_queue)
{
	int size;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &queue->mutex);
	pthread_mutex_lock(&queue->mutex);

	size = fragment_queue ? queue->fragment_count : queue->block_count;

	printf("Max size unlimited, size %d%s\n", size,
						size == 0 ? " (EMPTY)" : "");

	pthread_cleanup_pop(1);
}


/* define cache hash tables */
#define CALCULATE_CACHE_HASH(N) (llabs(N) & 0xffff)

/* Called with the cache mutex held */
INSERT_HASH_TABLE(cache, struct cache, CALCULATE_CACHE_HASH, index, hash)

/* Called with the cache mutex held */
REMOVE_HASH_TABLE(cache, struct cache, CALCULATE_CACHE_HASH, index, hash);

/* define cache free list */

/* Called with the cache mutex held */
INSERT_LIST(free, struct file_buffer)

/* Called with the cache mutex held */
REMOVE_LIST(free, struct file_buffer)


struct cache *cache_init(int buffer_size, int max_buffers, int noshrink_lookup,
	int first_freelist)
{
	struct cache *cache = malloc(sizeof(struct cache));

	if(cache == NULL)
		MEM_ERROR();

	cache->max_buffers = max_buffers;
	cache->buffer_size = buffer_size;
	cache->count = 0;
	cache->used = 0;
	cache->free_list = NULL;

	/*
	 * The cache will grow up to max_buffers in size in response to
	 * an increase in readhead/number of buffers in flight.  But
	 * once the outstanding buffers gets returned, we can either elect
	 * to shrink the cache, or to put the freed blocks onto a free list.
	 *
	 * For the caches where we want to do lookup (fragment/writer),
	 * a don't shrink policy is best, for the reader cache it
	 * makes no sense to keep buffers around longer than necessary as
	 * we don't do any lookup on those blocks.
	 */
	cache->noshrink_lookup = noshrink_lookup;

	/*
	 * The default use freelist before growing cache policy behaves
	 * poorly with appending - with many duplicates the caches
	 * do not grow due to the fact that large queues of outstanding
	 * fragments/writer blocks do not occur, leading to small caches
	 * and un-uncessary performance loss to frequent cache
	 * replacement in the small caches.  Therefore with appending
	 * change the policy to grow the caches before reusing blocks
	 * from the freelist
	 */
	cache->first_freelist = first_freelist;

	memset(cache->hash_table, 0, sizeof(struct file_buffer *) * 65536);
	pthread_mutex_init(&cache->mutex, NULL);
	pthread_cond_init(&cache->wait_for_free, NULL);

	return cache;
}


struct file_buffer *cache_lookup(struct cache *cache, long long index)
{
	/* Lookup block in the cache, if found return with usage count
 	 * incremented, if not found return NULL */
	int hash = CALCULATE_CACHE_HASH(index);
	struct file_buffer *entry;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &cache->mutex);
	pthread_mutex_lock(&cache->mutex);

	for(entry = cache->hash_table[hash]; entry; entry = entry->hash_next)
		if(entry->index == index)
			break;

	if(entry) {
		/* found the block in the cache, increment used count and
 		 * if necessary remove from free list so it won't disappear
 		 */
		if(entry->used == 0) {
			remove_free_list(&cache->free_list, entry);
			cache->used ++;
		}
		entry->used ++;
	}

	pthread_cleanup_pop(1);

	return entry;
}


static struct file_buffer *cache_freelist(struct cache *cache)
{
	struct file_buffer *entry = cache->free_list;

	remove_free_list(&cache->free_list, entry);

	/* a block on the free_list is hashed */
	remove_cache_hash_table(cache, entry);

	cache->used ++;
	return entry;
}


static struct file_buffer *cache_alloc(struct cache *cache)
{
	struct file_buffer *entry = malloc(sizeof(struct file_buffer) +
							cache->buffer_size);
	if(entry == NULL)
			MEM_ERROR();

	entry->cache = cache;
	entry->free_prev = entry->free_next = NULL;
	cache->count ++;
	return entry;
}


static struct file_buffer *_cache_get(struct cache *cache, long long index,
	int hash)
{
	/* Get a free block out of the cache indexed on index. */
	struct file_buffer *entry = NULL;
 
	pthread_cleanup_push((void *) pthread_mutex_unlock, &cache->mutex);
	pthread_mutex_lock(&cache->mutex);

	while(1) {
		if(cache->noshrink_lookup) {	
			/* first try to get a block from the free list */
			if(cache->first_freelist && cache->free_list)
				entry = cache_freelist(cache);
			else if(cache->count < cache->max_buffers) {
				entry = cache_alloc(cache);
				cache->used ++;
			} else if(!cache->first_freelist && cache->free_list)
				entry = cache_freelist(cache);
		} else { /* shrinking non-lookup cache */
			if(cache->count < cache->max_buffers) {
				entry = cache_alloc(cache);
				if(cache->count > cache->max_count)
					cache->max_count = cache->count;
			}
		}

		if(entry)
			break;

		/* wait for a block */
		pthread_cond_wait(&cache->wait_for_free, &cache->mutex);
	}

	/* initialise block and if hash is set insert into the hash table */
	entry->used = 1;
	entry->error = FALSE;
	if(hash) {
		entry->index = index;
		insert_cache_hash_table(cache, entry);
	}

	pthread_cleanup_pop(1);

	return entry;
}


struct file_buffer *cache_get(struct cache *cache, long long index)
{
	return _cache_get(cache, index, 1);
}


struct file_buffer *cache_get_nohash(struct cache *cache)
{
	return _cache_get(cache, 0, 0);
}


void cache_rehash(struct file_buffer *entry, long long index)
{
	struct cache *cache = entry->cache;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &cache->mutex);
	pthread_mutex_lock(&cache->mutex);

	if(cache->noshrink_lookup) {
		remove_cache_hash_table(cache, entry);
		entry->index = index;
		insert_cache_hash_table(cache, entry);
	}

	pthread_cleanup_pop(1);
}


void cache_block_put(struct file_buffer *entry)
{
	struct cache *cache;

	/*
	 * Finished with this cache entry, once the usage count reaches zero it
 	 * can be reused.
	 *
	 * If noshrink_lookup is set, put the block onto the free list.
 	 * As blocks remain accessible via the hash table they can be found
 	 * getting a new lease of life before they are reused.
	 *
	 * if noshrink_lookup is not set then shrink the cache.
	 */

	if(entry == NULL)
		return;

	cache = entry->cache;

	pthread_cleanup_push((void *) pthread_mutex_unlock, &cache->mutex);
	pthread_mutex_lock(&cache->mutex);

	entry->used --;
	if(entry->used == 0) {
		if(cache->noshrink_lookup) {
			insert_free_list(&cache->free_list, entry);
			cache->used --;
		} else {
			free(entry);
			cache->count --;
		}

		/* One or more threads may be waiting on this block */
		pthread_cond_signal(&cache->wait_for_free);
	}

	pthread_cleanup_pop(1);
}


void dump_cache(struct cache *cache)
{
	pthread_cleanup_push((void *) pthread_mutex_unlock, &cache->mutex);
	pthread_mutex_lock(&cache->mutex);

	if(cache->noshrink_lookup)
		printf("Max buffers %d, Current size %d, Used %d,  %s\n",
			cache->max_buffers, cache->count, cache->used,
			cache->free_list ?  "Free buffers" : "No free buffers");
	else
		printf("Max buffers %d, Current size %d, Maximum historical "
			"size %d\n", cache->max_buffers, cache->count,
			cache->max_count);

	pthread_cleanup_pop(1);
}

INSERT_LIST(fragment, struct frag_locked)
REMOVE_LIST(fragment, struct frag_locked)