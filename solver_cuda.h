//#define NDEBUG
#include <cassert>
#include <stdio.h>
#define WORK_SHARE 
#define WARP_SIZE 32
#define PERMUTATE_VARS_ORDER

//#define SHUFFLE_SHARDS 
//#define EQUAL_THREADS_IN_WARP
//#define FORCE_SERIALIZE


#define DEFAULT_BLOCKSIZE 128
#define DEFAULT_VOTE_THRESHOLD 0
//#define CACHE_MODE cudaFuncCachePreferL1
#define CACHE_MODE cudaFuncCachePreferShared
#define m_CopyToGPU(d, s,  bytes){ CudaSafeCall(cudaMalloc((void**) &d, bytes)); CudaSafeCall(cudaMemcpy((void*) d, (void*)s, bytes, cudaMemcpyHostToDevice)); }
#define m_CopyToGPU_0(d, s, bytes,  num_inst){ CudaSafeCall(cudaMalloc((void**) &d, bytes*num_inst)); CudaSafeCall(cudaMemcpy((void*) d, (void*)s, bytes, cudaMemcpyHostToDevice)); }

#define ROOT_READY       0x01000000
#define ROOT_NOT_READY   0x02000000
#define ROOT_STOLEN      0x03000000
#define THREADSTATE_MASK 0xffff0000


#define HIDDEN_REASONS_SIZE (3*c.pl_size/2)

#define SDD int4& inspects,\
	int& shard_num,\
	const   Rcnf&  c,\
	var_word* ws,\
	var_word* vars,\
	const int& stride,\
	trailword* trail,\
	int& trail_end,\
	int& BCP_queue_front,\
	int& decision_var_index,\
	RESULT& state,\
	int& stall_count,\
	int& stalled_start,\
	int& stalled_end,\
	varind& stalled_var_index,\
	var_word& wsword,\
	int& root_trailpos,\
	shadowword* shadow_reasons,\
	int& shadow_reasons_end,\
	volatile threadstate* thread_state,\
	volatile solver_internal_vars* employer_transfer_vars,\
	varind* vars_heap,\
	const int& inspects_limit


#define SDA inspects,\
	shard_num,\
	c,\
	ws,\
	vars,\
	stride,\
	trail,\
	trail_end,\
	BCP_queue_front,\
	decision_var_index,\
	state,\
	stall_count,\
	stalled_start,\
	stalled_end,\
	stalled_var_index,\
	wsword,\
	root_trailpos,\
	shadow_reasons,\
	shadow_reasons_end,\
	thread_state,\
	employer_transfer_vars,\
	vars_heap,\
	inspects_limit

struct __align__(16) solver_internal_vars{
	RESULT state;
	int trail_end;
	int root_trailpos;
	int BCP_queue_front;
	int decision_var_index;
};

typedef uint threadstate;

static inline double cpuTime(void) { return (double)clock() / CLOCKS_PER_SEC; } 
__device__ unsigned int lanemask_lt(){
	unsigned int mask;
	asm("mov.u32 %0, %lanemask_lt;" : "=r"(mask));
	return mask;
}

/*
__device__ __inline__ int ld_gbl_int(const double *addr) {
	double return_value;
	asm("ld.global.cg.f64 %0, [%1];" : "=r"(return_value) : "r"(addr));
	return return_value;
}
*/

__device__ inline int my_warp_num(){return (threadIdx.x+blockIdx.x*blockDim.x)/WARP_SIZE;}
__device__ inline int warpIdx(){return threadIdx.x/WARP_SIZE;}
__device__ inline int threadWidx(){return threadIdx.x&(uint)(WARP_SIZE-1);}

