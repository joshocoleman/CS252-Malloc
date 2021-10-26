#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/*Helper function that keeps track of the index of the original header
 */
static inline int indexUpdate(size_t actual_size) {
  int index = ((actual_size - ALLOC_HEADER_SIZE)/8) - 1; //gets the index after taking out of the header size/8
  if (index < 0 || index >= N_LISTS) { //makes sure that the index doesnt go out of bounds
     index = N_LISTS - 1;
  }
  return index;
}


/* Helper function that updates the header fields after splitting a block.
 */
static inline void splitUpdate(header * hdr, header * newHdr, size_t actual_size) {
  
  int index = indexUpdate(get_size(hdr)); //gets the original index
 
  set_size(hdr, get_size(hdr) - actual_size); //hdr should have the offset size
  newHdr->left_size = get_size(hdr); //the left size is updated
  set_size(newHdr, actual_size); //the new block B should have the actual size
  set_state(newHdr, ALLOCATED); //now allocated
  get_right_header(newHdr)->left_size = actual_size;

  int newIndex = indexUpdate(get_size(hdr)); //updates the index
  header *freelist = &freelistSentinels[newIndex]; //temp
  if (index == newIndex) { //index is the same, don't change/remove
    return;
  }
  else { //index is changed, freelistSentinel should point at a different header
    hdr->prev->next = hdr->next; //the one before hdr's next should be hdr's next
    hdr->next->prev = hdr->prev; //the one after hdr's prev should be hdr's prev
    if (freelist == freelist->next) { //if emptt/pointing back at itself
      freelist->next = hdr; //insert
      freelist->prev = hdr;
      hdr->next = freelist;
      hdr->prev = freelist;
    }
    else { //insert in the beginning
    hdr->prev = freelist;
    hdr->next = freelist->next;
    freelist->next->prev = hdr;
    freelist->next = hdr;
    }
  }
  return;
 
}

static inline void coalesce(header * hdr, header * neighbor) {
  int orgIndex = indexUpdate(get_size(hdr));
  set_size(hdr, get_size(neighbor) + get_size(hdr)); //merge the sizes
  set_state(hdr, UNALLOCATED);
  set_state(neighbor, UNALLOCATED);
  header * temp = get_right_header(neighbor); //temp
  temp->left_size = get_size(hdr);

  neighbor->prev->next = neighbor->next; //removes
  neighbor->next->prev = neighbor->prev;
  neighbor->next = NULL;
  neighbor->prev = NULL;

  int newIndex = indexUpdate(get_size(hdr));
  if (orgIndex == newIndex) { //index is the same, don't change/remove
    return;
  } 
  else { //index is changed, freelistSentinel should point at a different header
    header *freelist = &freelistSentinels[newIndex];
    if (freelist == freelist->next) { //if empty
      freelist->next = hdr; //insert
      freelist->prev = hdr;
      hdr->next = freelist;
      hdr->prev = freelist;
    }
    else { //if not empty, insert in the beginning
    hdr->prev = freelist;
    hdr->next = freelist->next;
    freelist->next->prev = hdr;
    freelist->next = hdr;
    }
  }
  return;
    
}

/*
static inline header * chunkUpdate(header * newChunk, size_t actual_size) {
  //newChunk NULL check
  if (newChunk == NULL) {
    return NULL;
  }
  //convinient vars
  header * left = get_left_header(newChunk);
  header * right = get_right_header(newChunk);
  header * end = get_left_header(lastFencePost); //last block in the freelist

  if (get_right_header(lastFencePost) != left) { //not adjacent to it
    set_size(newChunk, get_size(newChunk));
    int newIndex = indexUpdate(get_size(newChunk)); //get the new index
    header * newLoc = &freelistSentinels[newIndex];
    //insertion
    if (newLoc == newLoc->next) { //if the place in the new index is empty
      newLoc->next = newChunk;
      newLoc->prev = newChunk;
      newChunk->prev = newLoc;
      newChunk->next = newLoc;
      insert_os_chunk(newChunk);
      return newChunk;
    }
   else { //insertion in the beginning of the sentinel list
      newChunk->prev = newLoc;
      newChunk->next = newLoc->next;
      newLoc->next->prev = newChunk;
      newLoc->next = newChunk;
      insert_os_chunk(newChunk);
      return newChunk;
    }
  }
  else if (get_right_header(lastFencePost) == left) { //if adjacent to it, coalesce
    int orgIndex = indexUpdate(get_size(get_left_header(lastFencePost))); //gets the original index of the 
    set_size(newChunk, get_size(newChunk) + (2 * ALLOC_HEADER_SIZE) + get_size(get_left_header(lastFencePost))); //inserts it in the beginning of the last block
    set_state(newChunk, UNALLOCATED);

    newChunk->left_size = get_size(get_left_header(get_left_header(lastFencePost)));
    int newIndex = indexUpdate(get_size(newChunk));

    if (orgIndex == newIndex) {
      return newChunk; 
    }

    header * newLoc = &freelistSentinels[newIndex];
 //insertion
    if (newLoc == newLoc->next) { //if the place in the new index is empty
      newLoc->next = newChunk;
      newLoc->prev = newChunk;
      newChunk->prev = newLoc;
      newChunk->next = newLoc;
      return newChunk;
    }
    else { //insertion in the beginning of the sentinel list
      newChunk->prev = newLoc;
      newChunk->next = newLoc->next;
      newLoc->next->prev = newChunk;
      newLoc->next = newChunk;
      return newChunk;
    }
    if (get_state(left) == UNALLOCATED) {
      int ogIndex = indexUpdate(get_size(left));
      set_size(newChunk, get_size(newChunk) + get_size(left) + (2 * ALLOC_HEADER_SIZE));
      set_state(newChunk, UNALLOCATED);

      newChunk->left_size = get_size(get_left_header(left));
      int nIndex = indexUpdate(get_size(newChunk));

      if (orgIndex == newIndex) {
        return newChunk;
      }

 //insertion
      if (newLoc == newLoc->next) { //if the place in the new index is empty
        newLoc->next = newChunk;
        newLoc->prev = newChunk;
        newChunk->prev = newLoc;
        newChunk->next = newLoc;
        return newChunk;
      }
      else { //insertion in the beginning of the sentinel list
        newChunk->prev = newLoc;
        newChunk->next = newLoc->next;
        newLoc->next->prev = newChunk;
        newLoc->next = newChunk;
        return newChunk;
      }
    }
  }
  

  return newChunk;
}
*/

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 z @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  if (raw_size == 0) {
    return NULL;
  }
  size_t remainder = raw_size % 8; //gets the remainder through modulo
  size_t actual_size = 0;
  if (remainder != 0) { //dont want to add 8 if the remainder isnt 0
    actual_size = (8 - remainder) + raw_size + ALLOC_HEADER_SIZE; //acounts for the remainder
  }
  else { //set the size as normal if the remainder is 0
    actual_size = raw_size + ALLOC_HEADER_SIZE;
  }

  if (actual_size < sizeof(header)) { //makes sure its bigger than the minimum header size
    actual_size = sizeof(header);
  }
  int index = indexUpdate(actual_size);
  
  header * hdr;
  header * current;

  for (int i = index; i < N_LISTS; i++) { //goes through the sentinel free list
    hdr = &freelistSentinels[i];
    current = &freelistSentinels[i];
    if (hdr->next == &freelistSentinels[i]) { //pointing at itself
      continue;
    }
    hdr = hdr->next; //checking the first sentinel
    while(1) {
      if (hdr == &freelistSentinels[i]) { //empty, pointing back
        break;
      }
      if (get_size(hdr) == actual_size || get_size(hdr) - actual_size < sizeof(header)) { //same size or less than the header size
        hdr->prev->next = hdr->next; //removes
	hdr->next->prev = hdr->prev;
	hdr->next = NULL;
	hdr->prev = NULL;
	set_state(hdr, ALLOCATED);
        return (header *) hdr->data;
      }
      if (get_size(hdr) - actual_size >= sizeof(header)) { //when split is needed
	header * newHdr = get_header_from_offset(hdr, get_size(hdr) - actual_size); //creates the header between the two chunks
        splitUpdate(hdr, newHdr, actual_size); //calls the helper function to split the block and fix the pointers
	return (header *) newHdr->data; //return the header with the allocated data
      }
      hdr = hdr->next; //iteration of the free list
    }
     //task 3, allocating chunks
    if (hdr == current) { //if more memory is needed
      header * newChunk = allocate_chunk(ARENA_SIZE); //get the new chunk
      if (newChunk == NULL) {
         return NULL;
      }
      //useful vars
      header * left = get_left_header(newChunk);
      header * right = get_right_header(newChunk);
      header * temp_fp = lastFencePost;
      lastFencePost = right; //new last fence post

      if (get_right_header(temp_fp) == left) { //adjacent chunks
        header * last = get_left_header(temp_fp);
        if (get_state(last) == UNALLOCATED) { //more coalescing is needed
	  int orgIndex = indexUpdate(get_size(last)); //get the original index
          set_size(last, get_size(last) + get_size(newChunk) + (2 * ALLOC_HEADER_SIZE));
	  right->left_size = get_size(last); //update the left size
	  int newIndex = indexUpdate(get_size(last)); //get the new index
	  if (orgIndex != newIndex) {
	    header * freelist = &freelistSentinels[newIndex];
	    //properly move the header
	    last->prev->next = last->next;
	    last->next->prev = last->prev;
            if (freelist == freelist->next) { //if this is empty, insert
              freelist->next = last;
              freelist->prev = last;
              last->next = freelist;
              last->prev = freelist;
            }
            else { //insertion for not empty sentinel
              last->prev = freelist;
              last->next = freelist->next;
              freelist->next->prev = last;
              freelist->next = last;
            }
	  }
        }
        else { //only the fenceposts needed coalescing
          set_size(temp_fp, get_size(newChunk) + (2 * ALLOC_HEADER_SIZE)); //just add two fenceposts' sizes
	  set_state(temp_fp, UNALLOCATED);
	  get_right_header(newChunk)->left_size = get_size(temp_fp);
	  header * freelist = &freelistSentinels[indexUpdate(get_size(temp_fp))];
          if (freelist == freelist->next) { //if this is empty, insert
            freelist->next = temp_fp;
            freelist->prev = temp_fp;
            temp_fp->next = freelist;
            temp_fp->prev = freelist;
          }
          else { //insertion for not empty sentinel
            temp_fp->prev = freelist;
            temp_fp->next = freelist->next;
            freelist->next->prev = temp_fp;
            freelist->next = temp_fp;
          }
        }
      }

      else {
        header * freelist = &freelistSentinels[indexUpdate(get_size(newChunk))];
        if (freelist == freelist->next) { //if this is empty, insert
          freelist->next = newChunk;
          freelist->prev = newChunk;
          newChunk->next = freelist;
          newChunk->prev = freelist;
        }
        else { //insertion for not empty sentinel
          newChunk->prev = freelist;
          newChunk->next = freelist->next;
          freelist->next->prev = newChunk;
          freelist->next = newChunk;
        }
       insert_os_chunk(get_left_header(newChunk)); //inserts it in the non adjacent list
      }
      return allocate_object(raw_size);
    }
    if (current != current->next) {
      hdr = current->next;
      break;
    }
  }
}
 


/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
//  header * hdr = ptr_to_header(p);
  if (p == NULL) { //do nothing
    return;
  }
  header * hdr = ptr_to_header(p);
  if (get_state(hdr) == UNALLOCATED) { //if the header given is already freed
    printf("Double Free Detected\n");
    assert(0);
    return;
  }
  set_state(hdr, UNALLOCATED);
  header * left = get_left_header(hdr);
  header * right = get_right_header(hdr);

  size_t leftSize = get_size(left);
  size_t rightSize = get_size(right);

  if (get_state(get_right_header(hdr)) != UNALLOCATED && get_state(get_left_header(hdr)) != UNALLOCATED) { //get left/right header
    int index = indexUpdate(get_size(hdr)); //get the index
    set_state(hdr, UNALLOCATED);
    header * freelist = &freelistSentinels[index];
    if (freelist == freelist->next) { //if this is empty, insert
      freelist->next = hdr;
      freelist->prev = hdr;
      hdr->next = freelist;
      hdr->prev = freelist;
    }
    else { //insertion for not empty sentinel
      hdr->prev = freelist;
      hdr->next = freelist->next;
      freelist->next->prev = hdr;
      freelist->next = hdr;
    }
   }
  else if (get_state(get_right_header(hdr)) == UNALLOCATED && get_state(get_left_header(hdr)) != UNALLOCATED) {
    coalesce(hdr, get_right_header(hdr)); //right header is absorbed, calls the helper function
  }
 
  else if (get_state(get_left_header(hdr)) == UNALLOCATED && get_state(get_right_header(hdr)) != UNALLOCATED) { //left header is added
    header *left = get_left_header(hdr); //uses a var for the header to the left
    int orgIndex = indexUpdate(get_size(left));

    set_size(left, get_size(hdr) + get_size(left)); //set the added size
    set_state(left, UNALLOCATED);
    get_right_header(left)->left_size = get_size(left); //fixes the pointer
 
 
    int newIndex = indexUpdate(get_size(left));
    if (orgIndex == newIndex) { //if the indexes are the same, no need to remove
      return;
    }
    else {
      header * freelist = &freelistSentinels[newIndex];
      left->prev->next = left->next; //removes
      left->next->prev = left->prev;
      left->next = NULL;
      left->prev = NULL; 
      if (freelist == freelist->next) { //if this is empty, insert
        freelist->next = left;
        freelist->prev = left;
        left->next = freelist;
        left->prev = freelist;
      }
      else { //insertion for not empty sentinel
        left->prev = freelist;
        left->next = freelist->next;
        freelist->next->prev = left;
        freelist->next = left;
      }
    }
  }

  else if (get_state(get_right_header(hdr)) == UNALLOCATED && get_state(get_left_header(hdr)) == UNALLOCATED) { //coalesce both sides
    header * neighbor = get_right_header(hdr);
    set_size(hdr, get_size(neighbor) + get_size(hdr)); //merge the sizes
    set_state(hdr, UNALLOCATED);
    set_state(neighbor, UNALLOCATED);
    get_right_header(neighbor)->left_size = get_size(hdr);

    neighbor->prev->next = neighbor->next; //removes
    neighbor->next->prev = neighbor->prev;
    neighbor->next = NULL;
    neighbor->prev = NULL;
  

    header *left = get_left_header(hdr); //uses a var for the header to the left
    int orgIndex = indexUpdate(get_size(left));

    set_size(left, get_size(hdr) + get_size(left)); //set the added size
    set_state(left, UNALLOCATED);
    set_state(hdr, UNALLOCATED);
    header * temp = get_right_header(left);
    temp->left_size = get_size(left); //fixes the pointer
  
    int newIndex = indexUpdate(get_size(left));
    if (orgIndex == newIndex) { //if the indexes are the same, no need to remove
      return;
    }
    else {
      header * freelist = &freelistSentinels[newIndex];
      left->prev->next = left->next; //removes
      left->next->prev = left->prev;
      left->next = NULL;
      left->prev = NULL; 
      if (freelist == freelist->next) { //if this is empty, insert
        freelist->next = left;
        freelist->prev = left;
        left->next = freelist;
        left->prev = freelist;
      }
      else { //insertion for not empty sentinel
        left->prev = freelist;
        left->next = freelist->next;
        freelist->next->prev = left;
        freelist->next = left;
      }
    } 
  }
 
}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
  if (get_state(chunk) != FENCEPOST) {
    fprintf(stderr, "Invalid fencepost\n");
    print_object(chunk);
    return chunk;
  }
	
  for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
    if (get_size(chunk)  != get_right_header(chunk)->left_size) {
      fprintf(stderr, "Invalid sizes\n");
      print_object(chunk);
      return chunk;
    }
  }
	
  return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
