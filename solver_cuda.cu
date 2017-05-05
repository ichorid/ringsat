#include "solver.h"
#include <signal.h>
#include <unistd.h>
#include "solver_cuda.h"
#include <stdio.h>
#include "cuda_error_check.cu"

// вставляем флаг CUDA перед определениями общих функций
#define CDF __device__
#include "solver_common.cu"

#define lane threadWidx()
#define SPIN_LIMIT (1<<25)
#define RNG_CYCLES 200


volatile sig_atomic_t e_flag = 0;

void SleepSomeTime(unsigned int ns)
{
	struct timespec t;
	t.tv_sec = 0;
	t.tv_nsec = (long)ns;
	nanosleep(&t, NULL);
}

__device__ uint GetRandomNumber(uint seed)
{
	for (int i=0; i<RNG_CYCLES; i++){
		//seed=(seed<<3)^(seed>>1);
		seed=(seed<<1)^((seed>>31)&1)^((seed>>29)&1)^((seed>>25)&1)^((seed>>24)&1);
	}
	return seed;
}
void INTHandler(int sig)
{
	e_flag = 1;
	/*
	signal(sig, SIG_IGN);
	const int stop_mark=1;
	cudaMemcpyToSymbolAsync(kernel_stop_signal, (void*)
				&stop_mark,
				sizeof(int), 0,
				cudaMemcpyHostToDevice, signal_stream);
	signal(SIGUSR1, INTHandler);
	*/
}

texture<int, cudaTextureType1D, cudaReadModeElementType> texPl;

cudaStream_t solver_kernel_stream;
cudaStream_t signal_stream;





__device__ int shnums_tmp[1<<14];

__device__ int complete_blocks=0;
__device__ int task_complete=0;
__device__ int4 shards_complete={0,0,0,0};
__device__ int4 warps_complete={0,0,0,0};
__device__ volatile int kernel_stop_signal=0; // флаг того, что нашлось решение.
//int4* warps_complete=NULL;


__device__ litind propagate_thread(SDD, 
		const int stall = DEFAULT_VOTE_THRESHOLD,
		const bool RemoveWatches = false)
{
	int i=0;
	varind var_index = 0 ;
	int pl_index = 0;
	int start = 0;
	int end = 0;
	litind conflict = 0;
	bool var_done=true;
	//while(!isBCPQueueEmpty(SDA, shard_num)){
	//while(__any(!isBCPQueueEmpty(SDA))){
	//while(__all(!isBCPQueueEmpty(SDA))){
	while(!isBCPQueueEmpty(SDA)){
		int nonempty_bcp_count=__popc(__ballot(!isBCPQueueEmpty(SDA)));
		// Голосование!
		if(!((nonempty_bcp_count > stall) || __any(stall_count!=0))){
			stall_count=0;
			if(!isBCPQueueEmpty(SDA) && !conflict && i!=end){
				stall_count=i;
				stalled_var_index=var_index;
				//pl_index = stalled_pl_index;
				stalled_start = start;
				stalled_end = end;
			}
			if(!isBCPQueueEmpty(SDA) && !conflict && i==end){
				stall_count=(-1);
			}
			break;
		}
		if(isBCPQueueEmpty(SDA)){
			continue;
			//break;
		}
		//берем очередную переменную из очереди (переменная уже означена)
		if(var_done){
			if(stall_count>0){
				var_index = stalled_var_index;
				start = stalled_start;
				end = stalled_end;
				i = stall_count;
				assert (stall_count>=start);
				assert (stall_count<end);
				stall_count=0;
			}else{
				var_index = getIndex(trail[stride*BCP_queue_front+shard_num]);
				assert(var_index<c.pl_size/2);
				pl_index = HVarToVar((1-2*GetVarphase(SDA, var_index))*var_index);
				start = c.pl[pl_index-1];
				end = c.pl[pl_index];
				i = start;
				wsword = ws[stride*bindex(i)+shard_num];
			}
			var_done=false;
		}
		while (!(wsword & (1 << (boffset(i))))&& (i<end)){
			i++;
			if(boffset(i)==0 && (i<end)){
				wsword = ws[stride*bindex(i)+shard_num];
			}
		}
		

		
		if (i==end){
			BCPQueuePopFront(SDA);//удаляем переменную из очереди
			//printf("\n STOP %i", var_index  );
			var_done=true;
			continue;
		}
#ifdef LITCACHE
		int bcpvar = CheckClause2(SDA, i);
#else
		int bcpvar = CheckClause(SDA, i);
#endif
		if (bcpvar==~0){
			conflict = (litind) i;
			BCPQueueClear(SDA);
			continue;
		}
		if (bcpvar!= 0){
			//assert(clauseUnit(SDA, i));
			assert((bcpvar>>1)>getIndex(trail[stride*root_trailpos+shard_num]));
			SetVar(SDA, bcpvar, (litind)i );

		}else{
			//assert(!clauseUnit(SDA, i));
		}
			//assert(!clauseEmpty(SDA, i));
		i++;
		if(boffset(i)==0 && (i<end)){
			wsword = ws[stride*bindex(i)+shard_num];
		}
	}
	if(isBCPQueueEmpty(SDA)){
		stall_count=0;
	}
	return conflict;
}


__device__ void CopyRootStateFromThread(SDD, const int src_shard_num)
{
	shadow_reasons_end=1;
	// очищаем текущее состояние
	while(trail_end>=1){
		trailword current = trail[stride*trail_end+shard_num];
		ClearVarset(SDA, getIndex(current));
		--trail_end;
	}
	BCPQueueClear(SDA);

	//копируем данные с донора
	root_trailpos=employer_transfer_vars[src_shard_num].root_trailpos;
	assert((getIndex(trail[stride*root_trailpos+src_shard_num]))<c.pl_size/2);
	for (int i=1; i<root_trailpos;i++){
		assert(((trail[stride*i+src_shard_num].var&VARINDEX_MASK)>>1)<c.pl_size/2);
		SetVar(SDA, trail[stride*i+src_shard_num].var&VARINDEX_MASK, 0,1);
	}
	//устанавливаем верхнюю корневую переменную
	SetVar(SDA, ((trail[stride*root_trailpos+src_shard_num].var)&VARINDEX_MASK)^1, 0,1);
	trail[stride*BCP_queue_front+shard_num].var|=SEEN_FLAG;
	decision_var_index = getIndex(trail[stride*root_trailpos+shard_num]); 
	assert(decision_var_index<c.pl_size/2);
	//if (shard_num==1) printf("\n DVI %i prev trail %i",decision_var_index, getIndex(trail[stride*(trail_end)+shard_num]));

	state=FORCED_DECISION;
}

__device__ void ShareWorkInMyWarp(SDD)
{
	volatile threadstate* tgt_lockp = &thread_state[shard_num];
	if (state==UNSAT) assert(thread_state[shard_num]!=ROOT_READY);
	const threadstate old_lockdata = (state==UNSAT) ? ROOT_NOT_READY:ROOT_READY;
	threadstate new_lockdata = old_lockdata;
	const threadstate thread_lock_signature= ROOT_NOT_READY; 
	__threadfence();
	const bool thread_locked=(atomicCAS((uint*)tgt_lockp, old_lockdata, thread_lock_signature) == old_lockdata);
	const bool iam_employer = ((state==BCP_OK ||
			state==FORCED_DECISION ||
			state==DEFAULT_DECISION ||
			state==BCP_STALL) &&
			!hasShadow(trail[stride*root_trailpos+shard_num]) && 
			thread_locked);
	const bool iam_jobless = ((state==UNSAT)&&thread_locked);
	const uint jobless_map = __ballot(iam_jobless);
	const uint employer_map= __ballot(iam_employer);
	const int jobless_count= __popc(jobless_map);
	const int employer_count= __popc(employer_map);
	if (jobless_count>0 && employer_count>0){
		//const int employer_count= WARP_SIZE - jobless_count;
		const int jobless_id = __popc(jobless_map&lanemask_lt());
		assert (jobless_id<WARP_SIZE);
		//const int employer_id = lane - jobless_id;
		int employer_id = __popc(employer_map&lanemask_lt());
		__shared__ int employer_id_array[DEFAULT_BLOCKSIZE];
		__shared__ int employer_root_trailpos_array[DEFAULT_BLOCKSIZE];
		__shared__ int employer_trailend_array[DEFAULT_BLOCKSIZE];
		
		// Перемешиваем номера, чтобы более-менее равномерно
		// работа внутри варпа распределялась
		if (iam_employer && employer_count>1){
			uint rng_state=GetRandomNumber(clock());
			int shift=abs(((int)rng_state)&31);
			employer_id=(employer_id+shift)%employer_count;
		}
		if(iam_employer && employer_id<jobless_count){

			// мне помогут
			assert(!iam_jobless);
			employer_id_array[employer_id+warpIdx()*WARP_SIZE] = lane;
			employer_root_trailpos_array[employer_id+warpIdx()*WARP_SIZE] = root_trailpos;
			employer_trailend_array[employer_id+warpIdx()*WARP_SIZE] = trail_end;
			//перемещаем корень
			trail[stride*root_trailpos+shard_num].var=trail[stride*root_trailpos+shard_num].var | SEEN_FLAG;
			new_lockdata=ROOT_NOT_READY;
			++inspects.z;
		}
		const int my_employer = employer_id_array[jobless_id+warpIdx()*WARP_SIZE];
		assert (my_employer<WARP_SIZE);
		const int employer_shard_num =
			my_employer + 
			warpIdx()*WARP_SIZE +
			blockIdx.x*blockDim.x;
		
		if(iam_jobless && jobless_id<employer_count){
			assert(!iam_employer);
			//я помогу
			//копируем данные с хозяина
			root_trailpos = employer_root_trailpos_array[jobless_id+warpIdx()*WARP_SIZE];
			trail_end = employer_trailend_array[jobless_id+warpIdx()*WARP_SIZE];
			BCPQueueClear(SDA);


			// Сбрасываем массив теневых причин
			shadow_reasons_end=1;
			//TODO: убрать лишнее копирование следа
			for (int i=0; i<c.pl_size/2;i++){
				trail[stride*i+shard_num]=trail[stride*i+employer_shard_num];
			}
			/*
			for (int i=0; i<c.pl_size/WORD_SIZE+1;i++){
				vars[stride*i+shard_num]=vars[stride*i+employer_shard_num];
			}
			*/
		}
		// кооперативно копируем с нанимателей на
		// рабочих данные через промежуточные переменные
		// в общей памяти
		//TODO: вынести в отдельную функцию копирования
		for (int i=0; i<c.lits_size/WORD_SIZE+1;i++){
			__shared__ var_word tmp[DEFAULT_BLOCKSIZE];
			if((employer_id<jobless_count) && iam_employer){
				tmp[employer_id+warpIdx()*WARP_SIZE]=ws[stride*i+shard_num];
			}
			if((jobless_id<employer_count) && iam_jobless){
				ws[stride*i+shard_num]=tmp[jobless_id+warpIdx()*WARP_SIZE];
			}
		}
		for (int i=0; i<c.pl_size/WORD_SIZE+1;i++){
			__shared__ var_word tmp[DEFAULT_BLOCKSIZE];
			if((employer_id<jobless_count) && iam_employer){
				tmp[employer_id+warpIdx()*WARP_SIZE]=vars[stride*i+shard_num];
			}
			if((jobless_id<employer_count) && iam_jobless){
				vars[stride*i+shard_num]=tmp[jobless_id+warpIdx()*WARP_SIZE];
			}
		}
		if(iam_jobless && jobless_id<employer_count){
			// очищаем лишние переменные, скопированные с хозяина
			while(trail_end>=root_trailpos){
				trailword current = trail[stride*trail_end+shard_num];
				ClearVarset(SDA, getIndex(current));
				--trail_end;
			}
			//top_decision_var_index=decision_var_index;

			//if (shard_num==1) printf("\n DVI %i prev trail %i",decision_var_index, getIndex(trail[stride*(trail_end)+shard_num]));
			assert(decision_var_index<c.pl_size/2);
			BCPQueueClear(SDA);
			// устанавливаем переменную верхнего уровня решения в фазу, обратную той, что была у хозяина
			SetVar(SDA, ((trail[stride*root_trailpos+employer_shard_num].var)&VARINDEX_MASK)^1, 0,1);
			trail[stride*BCP_queue_front+shard_num].var|=SEEN_FLAG;
			decision_var_index = getIndex(trail[stride*root_trailpos+shard_num]); 
			state=FORCED_DECISION;
			
			/*
			if (my_employer==3 || my_employer==5 || shard_num==3 || shard_num == 5)
					printf("\n block %i lane %i employs lane %i : erv %i wdvi %i ",
					blockIdx.x, my_employer,
					lane,
					getIndex(sd.trail[sd.stride*root_trailpos+employer_shard_num]),
					decision_var_index) ;
					*/
					
			atomicAdd(&shards_complete.x,1);
			new_lockdata=ROOT_NOT_READY;
		}
	}
	__threadfence();
	if (thread_locked){
		thread_state[shard_num]=new_lockdata;
	}
}



__device__ bool TryExchangeWithThread(SDD, const int tgt_thread)
{
	volatile threadstate* tgt_lockp=  &thread_state[tgt_thread];
	const threadstate old_lockdata = thread_state[tgt_thread];
	const threadstate my_steal_signature= (shard_num | ROOT_STOLEN); 

	// проверим готовность партнера
	if((old_lockdata&THREADSTATE_MASK)!=ROOT_READY){
		//printf("\n thread %i old lockdata %x", shard_num, old_lockdata);
		return false;
	}
	// предложим обмен
	if(!atomicCAS((uint*)tgt_lockp, old_lockdata, my_steal_signature) == old_lockdata){
		// кто-то перехватил предложение
		assert(false);
		return false;
	}
	__threadfence();
	return true;
}

__device__  void PermutateNums(int multi, const float num_permutations = 2){
	//return;
	//uint rng_state=GetRandomNumber(clock()^shard_num);
	//uint rng_state=GetRandomNumber(123456789^(shard_num>>5));
	uint rng_state=GetRandomNumber(123456789);
	//uint rng_state=GetRandomNumber(123456789);
	for(int i=0; i<multi; i++){
		shnums_tmp[i]=i;
	}
	for(int i=0; i<multi; i++){

		rng_state=GetRandomNumber(rng_state);
		int x_address=  ((float)(rng_state&0x0fffffff) /
				(float)0x0fffffff) * (multi-1);
		assert(x_address > 0);
		assert(x_address < multi);
		rng_state=GetRandomNumber(rng_state);
		int y_address=  ((float)(rng_state&0x0fffffff) /
				(float)0x0fffffff) * (multi-1);
		assert(y_address > 0);
		assert(y_address < multi);
		varind x = shnums_tmp[x_address];
		varind y = shnums_tmp[y_address];
		shnums_tmp[x_address] = y;
		shnums_tmp[y_address] = x;
	}
	//for(int i=1; i<multi; i++){ printf("\n SHNUM %u",shnums_tmp[i]); }
}

__device__  void PermutateVarsShard(SDD, const float num_permutations = 2){
	//return;
#ifndef EQUAL_THREADS_IN_WARP
	uint rng_state=GetRandomNumber(123456789^shard_num);
#else
	uint rng_state=GetRandomNumber(123456789^(shard_num>>5));
#endif
	//uint rng_state=GetRandomNumber(123456789^shard_num);
	//uint rng_state=GetRandomNumber(123456789);
	for(int i=1; i<c.pl_size/2*num_permutations; i++){
		rng_state=GetRandomNumber(rng_state);
		int x_address= 1+ ((float)(rng_state&0x0fffffff) /
				(float)0x0fffffff) * (c.pl_size/2-1);
		assert(x_address > 0);
		assert(x_address < c.pl_size/2);
		rng_state=GetRandomNumber(rng_state);
		int y_address= 1+ ((float)(rng_state&0x0fffffff) /
				(float)0x0fffffff) * (c.pl_size/2-1);
		assert(y_address > 0);
		assert(y_address < c.pl_size/2);
		varind x = vars_heap[stride*x_address+shard_num];
		varind y = vars_heap[stride*y_address+shard_num];
		vars_heap[stride*x_address+shard_num] = y;
		vars_heap[stride*y_address+shard_num] = x;
	}
	/*
	printf("\n RNG %u",rng_state);
	for(int i=0; i<100; i++){
	if (shard_num==0)
		printf("\n var %i  %i", i, vars_heap[stride*i+shard_num]);
	if (shard_num==1)
		printf("\n var %i  %i", i, vars_heap[stride*i+shard_num]);
	}
	*/
	
#ifndef NDEBUG
	for(int i=0; i<c.pl_size/2; i++){
		bool varfound=false;
		for(int m=0; m<c.pl_size/2; m++){
			if(vars_heap[stride*m+shard_num]==i){
				varfound=true;
				break;
			}
		}
		assert(varfound);
	}
#endif
}
__global__ void __launch_bounds__(DEFAULT_BLOCKSIZE,8) PreprocessR(
		gpusolverdata sd,
		shadowword* shadow_reasons,
		volatile threadstate* thread_state,
	       	gpusolverdata sd_temp,
		int first_trail_end,
		int first_BCP_queue_front,
		int* partial_warps,
		volatile solver_internal_vars* employer_transfer_vars,
		const int subproblem=0)
{
	const int inspects_limit=1<<30;

	int shard_num = threadIdx.x+blockIdx.x*blockDim.x;
	//printf("\n Preprocess START  ");

	//uint trail_end = first_trail_end;
	
	//if(threadIdx.x==0){
	/*
	for(int i=0; i<WARP_SIZE;i++){
		partial_warps[i]=0;
	}
	*/
	//sd.conflict_count_old[shard_num]=555555;
	//sd.stall_count[shard_num]=0;
	sd.out[shard_num]=BCP_OK;
	sd.inspects[shard_num].x=0;
	sd.inspects[shard_num].y=0;
	sd.inspects[shard_num].z=0;
	sd.inspects[shard_num].w=0;
	sd.decision_var_index[shard_num]=0;
	sd.trail_end[shard_num]=first_trail_end;
	/*
	for(int i=0;i<BCP_QUEUE_SIZE;i++){
		sd.BCP_queue[shard_num][i]=444444;
	}
	*/
	//__threadfence();

	varind* vars_heap=sd.vars_heap;

	shards_complete.x=0;
	shards_complete.y=0;
	shards_complete.z=0;
	shards_complete.w=0;
	warps_complete.x=0;
	warps_complete.y=0;
	warps_complete.z=0;
	warps_complete.w=0;
	for (int i=0; i<sd.c.pl_size/2;i++){
		//assert(abs((int)(sd_temp.trail[i]))<sd.c.pl_size/2);
		sd.trail[sd.stride*i+shard_num]=sd_temp.trail[i];
		//if(shard_num==26){printf("\n tv %i %i", i, getIndex(sd_temp.trail[i]));} }
		sd.vars_heap[sd.stride*i+shard_num]=i;
	}
	
	for (int i=0; i<sd.c.pl_size/WORD_SIZE+1;i++){
		sd.vars[sd.stride*i+shard_num]=sd_temp.vars[i];
	}

	for (int i=0; i<sd.c.lits_size/WORD_SIZE+1;i++){
		//sd.ws[(sd.c.lits_size/WORD_SIZE+1)*shard_num+i]=sd_temp.ws[i];
		sd.ws[sd.stride*i+shard_num]=sd_temp.ws[i];
	}

	int4 inspects=sd.inspects[shard_num];
	RESULT state=sd.out[shard_num];
	int trail_end=sd.trail_end[shard_num];
	int decision_var_index=sd.decision_var_index[shard_num];
	//int BCP_queue_front=sd.BCP_queue_front[shard_num];
	int BCP_queue_front=first_BCP_queue_front;
	int stall_count=0;
	int stalled_start, stalled_end;
	varind stalled_var_index;
	var_word wsword;

	int shadow_reasons_end = 1;

	//bool move_root=false;
	//int root_trailpos=trail_end;
	int root_trailpos=0;
	sd.trail[sd.stride*root_trailpos+shard_num].var=0;
	const int stride=sd.stride;
	Rcnf& c = sd.c;
	var_word* &ws=sd.ws;
	var_word* &vars=sd.vars;
	trailword* &trail=sd.trail;


	//assert(!verifytrail(sd, shard_num));
	//BCPQueueClear(SDA);
	
	//printf("\n TRAILEND_GPU %i",trail_end);
	// Дефолтная фаза
	for (int i=0; i<sd.c.pl_size/2;i++){
		if(!GetVarset(SDA, i)){
	 		SetVarphase(SDA, i);
	 		//ClearVarphase(SDA, i);
			}
	}
/*	
	for(int j=0;j<13;j++){
		varind nfv = findNextFreeVar(SDA, j+1);
		if ((subproblem>>j)&1){
			nfv = findNextFreeVar(SDA, nfv+1);
		}
		SetVar(SDA, HVarToVar(nfv));
		bool conflict=propagate_thread(SDA, 0);
		BCPQueueClear(SDA);
		if (conflict){
			state = UNSAT;
			//printf("\n Prop Stop");
			atomicAdd(&shards_complete.y,1);
			break;
		} else{
			if (trail_end==(c.pl_size/2-1)){
				state = SAT;
				atomicAdd(&shards_complete.x,1);
				//printf("\n %i Trail end %i", shard_num, trail_end);
				break;
			}
		}
	}
*/	
	
#ifdef PERMUTATE_VARS_ORDER
	PermutateVarsShard(SDA);
#endif
	
	for(uint j=0;j<sd.multi;j++){
	//for(uint j=0;j<0;j++){
	//for(uint j=0;j<5;j++){
#ifndef EQUAL_THREADS_IN_WARP
		int nfv = findNextFreeVar(SDA, 1)*(1-2*((shard_num>>j)&1));
#else
		int nfv = findNextFreeVar(SDA, 1)*(1-2*((shard_num>>(sd.multi-j+4))&1));
#endif 
		//int nfv = findNextFreeVar(SDA, 1)*(1-2*((shard_num>>(sd.multi-j-1))&1));
		
		/*	
		varind nfv = findNextFreeVar(SDA, j+1);
		if ((shard_num>>j)&1){
			nfv = findNextFreeVar(SDA, nfv+1);
		}
		*/
		
		
		//assert(!searchTrail(sd, shard_num, nfv ));
		//nfv = 32;
		//if(threadWidx()==0) printf("\n Thread %i nfv %i", threadIdx.x, nfv);
		//BCP_queue_pushbackR(sd, shard_num, nfv);
		//bool RemoveWatches=true;
		bool RemoveWatches=false;
		SetVar(SDA, HVarToVar(nfv),0,1);
		//__syncthreads();
		//BCP_queuePrint(sd, shard_num);
		
		litind conflict = propagate_thread(SDA, 0, RemoveWatches);
		BCPQueueClear(SDA);
		if (conflict!=0){
			state = UNSAT;
			//printf("\n Prop Stop %i", threadIdx.x);
			atomicAdd(&shards_complete.y,1);
			break;
		} else{
			for(int i=2; i<c.lits_size; i++){
				if(c.lits[i].x!=NO_LITIND){
					if(clauseUnit(SDA, i)){
						if(shard_num==3){
							DBGPrintClause(SDA, i);
						}
						assert(clauseEmpty(SDA, i));
						assert(false);
					}
				}
			}
			//printf("\n %i Trail end %i", shard_num, trail_end);
			if (trail_end==(c.pl_size/2-1)){
				state = SAT;
				atomicAdd(&shards_complete.x,1);
				//printf("\n %i Trail end %i", shard_num, trail_end);
				break;
			}
		}
	}
/*
	sd.inspects[shard_num].x=0;
	sd.inspects[shard_num].y=0;
	sd.inspects[shard_num].z=0;
	sd.inspects[shard_num].w=0;
	*/
	sd.inspects[shard_num].x+=inspects.x;
	sd.inspects[shard_num].y+=inspects.y;
	sd.inspects[shard_num].z+=inspects.z;
	sd.out[shard_num]=state;
	sd.trail_end[shard_num]=trail_end;

	sd.decision_var_index[shard_num]=decision_var_index;
	sd.BCP_queue_front[shard_num]=BCP_queue_front;
	
	thread_state[shard_num]=ROOT_NOT_READY;
	//printf("\n Thread %i PP result %i , inspects %i",threadIdx.x, result, sd.inspects[shard_num]);
	//printf("\n %i Trail end %i", shard_num, trail_end);
	//PermutateVarsShard(SDA);
	//shnums_tmp[shard_num]=shard_num; 
	if (shard_num==0) PermutateNums(1<<sd.multi); 

}

__device__ void StoreLocalVars(SDD)
{
	employer_transfer_vars[shard_num].state=state;
	employer_transfer_vars[shard_num].trail_end=trail_end;
	employer_transfer_vars[shard_num].root_trailpos=root_trailpos;
	employer_transfer_vars[shard_num].BCP_queue_front=BCP_queue_front;
	employer_transfer_vars[shard_num].decision_var_index=decision_var_index;
}
__device__ void LoadLocalVars(SDD)
{
	state=employer_transfer_vars[shard_num].state;
	trail_end=employer_transfer_vars[shard_num].trail_end;
	root_trailpos=employer_transfer_vars[shard_num].root_trailpos;
	BCP_queue_front=employer_transfer_vars[shard_num].BCP_queue_front;
	decision_var_index=employer_transfer_vars[shard_num].decision_var_index;
}


__device__ bool CheckSAT(SDD)
{
	assert(isBCPQueueEmpty(SDA));
	if (trail_end==(c.pl_size/2-1)){
		assert(!verifytrail(SDA));
		assert(!DBGVerifyVars(SDA));
		for(int i=2; i<c.lits_size; i++){
			if(c.lits[i].x!=NO_LITIND){
				if(!clauseSolved(SDA, i)){
					assert(clauseEmpty(SDA, i));
					if(shard_num==1){
						DBGPrintClause(SDA, i);
					}
					assert(false);

				}
			}
		}
			
		//atomicAdd(&shards_complete.x,1);
		return true;
	}
	return false;
}
__device__ void MakeNewDecision(SDD)
{
	assert(isBCPQueueEmpty(SDA));
	DefineDecisionVar(SDA);
	//ставим в очередь BCP переменную уровня решения
	assert(decision_var_index<c.pl_size/2);
	SetVar(SDA, HVarToVar((int)decision_var_index* (-1+2*(GetVarphase(SDA, decision_var_index)))), 0, 1);
	
	//assert(!searchTrail(SDA, shard_num, decision_var_index[shard_num]));
	if(thread_state[shard_num]==ROOT_NOT_READY){
		trail[stride*root_trailpos+shard_num].var=trail[stride*root_trailpos+shard_num].var | SEEN_FLAG;
		//переставляем корень
		int new_root_trailpos = FindNewRoot(SDA);
		assert(new_root_trailpos!=0);
		root_trailpos = new_root_trailpos;
		StoreLocalVars(SDA);
		thread_state[shard_num]=ROOT_READY;
		++inspects.w;
	}
	assert(!hasShadow(trail[stride*root_trailpos+shard_num]));
	assert( isDecision(trail[stride*root_trailpos+shard_num]));
}
__device__ bool StealWorkFromOtherWarps(SDD)
{
#ifdef WORK_SHARE
	uint rng_state=GetRandomNumber(clock());
	//uint rng_state=GetRandomNumber(my_warp_num());
	//int donor_warp=(stride/WARP_SIZE-1)&GetRandomNumber(rng_state);
	for(int safe_counter=0; safe_counter<100000; safe_counter++){
		if (__any(warps_complete.w==(stride/WARP_SIZE)
					||
					kernel_stop_signal!=0) ){
			// все отрешалось, ловить нечего
			break;
		}
		//const int donor_thread=WARP_SIZE*donor_warp+safe+lane;


		rng_state=GetRandomNumber(rng_state^lane);
		// выбираем случайный варп для обмена и от него
		// линейно сканируем направо с wrap'ом
		//if (lane==0 && shard_num/32==63) printf(" \n state %i  donor warp %i", thread_state[shard_num], donor_warp);
		for (int i=0; i<10; i++){
			rng_state=GetRandomNumber(rng_state);
		}
		/*
		const int random_shift=(int)((WARP_SIZE-1)&rng_state);
		const int donor_thread=random_warps_per_lane_base+random_shift;
		*/
		const int donor_thread=WARP_SIZE*
			//((stride/WARP_SIZE-1)&donor_warp)
			//donor_warp
			//((63)&(int)rng_state)
			// база
			lane*(gridDim.x*DEFAULT_BLOCKSIZE/WARP_SIZE/WARP_SIZE)
		+
		//FIXME constants! sizing!
		// рандомный сдвиг 
		(int)((gridDim.x*DEFAULT_BLOCKSIZE/WARP_SIZE-1)&rng_state);
		//lane;
		//if (lane==0) printf(" \n donor thread %i  donor warp %i", donor_thread ,donor_warp);
		assert(donor_thread<(gridDim.x*DEFAULT_BLOCKSIZE));
	
		if(thread_state[shard_num]==ROOT_NOT_READY &&
				TryExchangeWithThread(SDA, donor_thread) 
				){
			//printf("\n t %i try t %i OK", shard_num, donor_thread);
			//atomicAdd(&sd.inspects[donor_thread].w,1);
			CopyRootStateFromThread(SDA, donor_thread);
			__threadfence();
			// разлочиваем тред-донор
			// FIXME  потенциальный баг! при
			// отключении этой строки повторные
			// обмены все равно иногда
			// встречаются!!!!!
			thread_state[donor_thread]=ROOT_NOT_READY;
		}
		__threadfence();
		if (__any(state==FORCED_DECISION)){
			if(lane==0){ atomicAdd(&warps_complete.y,1); }
			if(lane==0){ atomicSub(&warps_complete.w,1); }
			//printf ("\n COPY COMPLETE");
			return true;
		}else{
			if(lane==0){
				atomicAdd(&warps_complete.z,1);
			}
			
			for (int i=0; i<50; i++){
				rng_state=GetRandomNumber(rng_state);
			}
		}
	}
#endif
	return false;
}
__device__ void MainSolverCycle(SDD)
{
	litind conflict_lit = 0;
	int cycles_passed=0;
	int decisions_made=0;
	do{
		//Check SAT
		if(state==BCP_OK && CheckSAT(SDA)){
			state=SAT;
		}
		//Check STOPPED
		if ( inspects.x>=inspects_limit || 
		//if ( inspects.x>=500000|| 
			decisions_made > DECISIONS_LIMIT || 
			kernel_stop_signal!=0){
			state=STOPPED;
		}
		if(__any(state==STOPPED || state==SAT)){  break; }
		if(__all(state==UNSAT)){ break; }

#ifdef FORCE_SERIALIZE
			for(int i=0;i<WARP_SIZE;i++)
				if(i==lane)
#endif
		if (state==BCP_OK){
			MakeNewDecision(SDA);
			decisions_made++;
			state = DEFAULT_DECISION;
		}

#ifdef FORCE_SERIALIZE
			for(int i=0;i<WARP_SIZE;i++)
				if(i==lane)
#endif
		if (state==CONFLICT){
			// Backtracking
			const int shadow_handle = BackjumpFast(SDA, conflict_lit);
			if (shadow_handle==~0){
				state=UNSAT;
			}else{
				//FIXME: оптимизировать и переделать в функцию
				assert(decision_var_index<c.pl_size/2);
				SetVar(SDA, HVarToVar((int)decision_var_index* (1-2*(GetVarphase(SDA, decision_var_index)))), shadow_handle, 1);
				trail[stride*BCP_queue_front+shard_num].var|=SEEN_FLAG;
				decisions_made++;
				state = FORCED_DECISION;
			}
		}
	
#ifdef WORK_SHARE
		ShareWorkInMyWarp(SDA);
#endif
		if(state==DEFAULT_DECISION || state==FORCED_DECISION || state==BCP_STALL){
			//Propagate
#ifdef FORCE_SERIALIZE
			for(int i=0;i<WARP_SIZE;i++)
				if(i==lane)
#endif
			conflict_lit=propagate_thread(SDA, DEFAULT_VOTE_THRESHOLD);
			if (conflict_lit!=0){
				BCPQueueClear(SDA);
				state=CONFLICT;
			}else{
				state = isBCPQueueEmpty(SDA) ?  BCP_OK : BCP_STALL;
			}
		}
	}while(++cycles_passed<=15000000);
}


__global__ void __launch_bounds__(DEFAULT_BLOCKSIZE,8) Solve(
		gpusolverdata sd,
		shadowword* shadow_reasons,
		volatile threadstate* thread_state,
		volatile solver_internal_vars* employer_transfer_vars,
		const int inspects_limit)
{
	int shard_num = threadIdx.x+blockIdx.x*blockDim.x;
#ifdef SHUFFLE_SHARDS
	shard_num = shnums_tmp[shard_num];
#endif
	//int shard_num = threadIdx.x*gridDim.x*gridDim.y+blockIdx.x;
	int4 inspects=sd.inspects[shard_num];
	RESULT state=sd.out[shard_num];
	int trail_end=sd.trail_end[shard_num];
	int decision_var_index=sd.decision_var_index[shard_num];
	int BCP_queue_front=sd.BCP_queue_front[shard_num];
	int stall_count=0;
	int stalled_start, stalled_end;
	varind stalled_var_index;
	var_word wsword;
	varind* vars_heap=sd.vars_heap;


	int shadow_reasons_end = 1;

	const int stride=sd.stride;
	Rcnf& c = sd.c;
	var_word* &ws=sd.ws;
	var_word* &vars=sd.vars;
	trailword* &trail=sd.trail;

	int root_trailpos = trail_end;

	// FIXME аццкий костыль!
	DefineDecisionVar(SDA);
	decision_var_index=0;


	for (int i=0; i<HIDDEN_REASONS_SIZE; i++){ shadow_reasons[shard_num*HIDDEN_REASONS_SIZE+i]=8888; }
	StoreLocalVars(SDA);

	thread_state[shard_num]=ROOT_NOT_READY;
	//if (lane==0)
	do{
		MainSolverCycle(SDA);
		if(lane==0){ 
			atomicAdd(&warps_complete.w,1);
		       	atomicAdd(&warps_complete.x,1);
		}
		if(__any(state==STOPPED || state==SAT) || warps_complete.w==(stride/WARP_SIZE)){
			// все отрешалось, ловить нечего
			thread_state[shard_num]=ROOT_NOT_READY;
			kernel_stop_signal=1;
		}
	}while(kernel_stop_signal==0 && __all(state==UNSAT) &&
			StealWorkFromOtherWarps(SDA));
	// ^ TODO: Сделать так, чтобы от перестановки условий
	// корректность не терялась. 
	if(state!=UNSAT  && state!=SAT){
		state=STOPPED;
	}
	sd.inspects[shard_num].x+=inspects.x;
	sd.inspects[shard_num].y+=inspects.y;
	sd.inspects[shard_num].z+=inspects.z;
	sd.inspects[shard_num].w+=inspects.w;
	sd.out[shard_num]=state;
}


RESULT SolverSolve(
		Rcnf &c,
		Rsolverstate &s,
		var_word* vars,
		var_word* ws,
		trailword* trail,
		const int multi,
		const int inspects_limit ,
		const int kernel_runs_limit ,
		const bool truncate ,
		const int subproblem)
{
	int blocksize =DEFAULT_BLOCKSIZE;
        cudaDeviceProp devProp;
        cudaGetDeviceProperties(&devProp, 0);

	const int num_inst = (1<<multi);
	// TODO: разобраться с тредами, выходящими за пределы блоков !!!
	//const int num_blocks_truncated = (num_inst - (num_inst%devProp.multiProcessorCount));
	const int num_blocks_truncated = (num_inst - (num_inst%8));
	int num_blocks;
	if (truncate){
		num_blocks = num_blocks_truncated;
	}else{
		num_blocks = num_inst;
	}
	//num_blocks=num_blocks/(blocksize/WARP_SIZE);
	//num_blocks=num_blocks/WARP_SIZE;
	//const int num_blocks = num_blocks_truncated ;

	//int trunc = (blocksize*num_multiprocessors);
	//cout << "\n trunc " << trunc;
	RESULT* out = (RESULT*) malloc(num_inst*sizeof(RESULT));
	
	gpusolverdata sd,sd_temp;
	RESULT result=UNSAT;
	int4* inspects = (int4*) malloc(num_inst*sizeof(int4));
	int4* pp_inspects = (int4*) malloc(num_inst*sizeof(int4));
	double copy_starttime=cpuTime();
	sd.multi=multi;
	sd.stride=1<<multi;
	sd.c.lits_size=c.lits_size;
	sd.c.pl_size=c.pl_size;
	sd.blocks_complete=0;


	//cudaMalloc((void**) &qqq, num_inst*sizeof(RESULT));
	//cudaMalloc((void**) &sd.out, num_inst*sizeof(RESULT));
	CudaSafeCall(cudaMalloc((void**) &sd.out, num_inst*sizeof(RESULT)));
	CudaSafeCall(cudaMalloc((void**) &sd.trail_end, num_inst*sizeof(int)));
	CudaSafeCall(cudaMalloc((void**) &sd.BCP_queue_front, num_inst*sizeof(int)));
	//CudaSafeCall(cudaMalloc((void**) &sd.BCP_queue_back, num_inst*sizeof(int)));
	CudaSafeCall(cudaMalloc((void**) &sd.decision_var_index, num_inst*sizeof(int)));
	CudaSafeCall(cudaMalloc((void**) &sd.inspects, num_inst*sizeof(int4)));
	//CudaSafeCall(cudaMalloc((void**) &sd.conflict_count_old, num_inst*sizeof(int)));
	//CudaSafeCall(cudaMalloc((void**) &sd.stall_count, num_inst*sizeof(int)));

	m_CopyToGPU(sd.c.pl, c.pl, c.pl_size*sizeof(litind));
	m_CopyToGPU(sd.c.lits, c.lits, c.lits_size*sizeof(uintx));

	CudaSafeCall(cudaMalloc((void**) &sd.ws, num_inst*sizeof(var_word)*s.ws_size));
	CudaSafeCall(cudaMalloc((void**) &sd.vars, num_inst*sizeof(var_word)*s.vars_size));
	CudaSafeCall(cudaMalloc((void**) &sd.trail, num_inst*sizeof(trailword)*c.pl_size/2));
	CudaSafeCall(cudaMalloc((void**) &sd.vars_heap,	num_inst*sizeof(varind)*c.pl_size/2));

	shadowword* shadow_reasons = NULL;
	CudaSafeCall(cudaMalloc((void**) &shadow_reasons, HIDDEN_REASONS_SIZE*num_inst*sizeof(shadowword)));

	volatile solver_internal_vars* employer_transfer_vars;
	CudaSafeCall(cudaMalloc((void**)&employer_transfer_vars, num_inst*sizeof(solver_internal_vars)));

	volatile threadstate* thread_state;
	CudaSafeCall(cudaMalloc((void**)&thread_state, (num_inst)*sizeof(threadstate)));

	CudaSafeCall(cudaMalloc((void**) &sd.trail, num_inst*sizeof(trailword)*c.pl_size/2));

	int* partial_warps = NULL;
	//CudaSafeCall(cudaMalloc((void**) &partial_warps, WARP_SIZE*sizeof(int)));
	//CudaSafeCall(cudaMalloc((void**) &sd.bcpstat, num_inst*sizeof(int)*BCPSTATSIZE));

	sd_temp=sd;
	//докопируем начальное заполнение

	m_CopyToGPU(sd_temp.ws, ws, sizeof(var_word)*s.ws_size);
	m_CopyToGPU(sd_temp.vars, vars, sizeof(var_word)*s.vars_size);
	m_CopyToGPU(sd_temp.trail, trail, sizeof(trailword)*c.pl_size/2);

	CudaSafeCall(cudaBindTexture(0, texPl, sd.c.pl, c.pl_size*sizeof(litind)));

	cudaEvent_t kernel_start, kernel_stop;
	cudaEventCreate(&kernel_start);
	cudaEventCreate(&kernel_stop);
	cudaEventRecord(kernel_start);

	cudaFuncSetCacheConfig(PreprocessR, CACHE_MODE );
	PreprocessR <<< num_blocks/DEFAULT_BLOCKSIZE, blocksize >>>
		(sd, shadow_reasons, thread_state, sd_temp, s.trail_end,
		 s.BCP_queue_front, partial_warps,
		 employer_transfer_vars, subproblem);
	//PreprocessR <<< 1, 32 >>> (sd,sd_temp, s.trail_end);

	cudaThreadSynchronize ();
	cudaEventRecord(kernel_stop);
	cudaEventSynchronize(kernel_stop);
	float preprocessTime;
	cudaEventElapsedTime(&preprocessTime, kernel_start, kernel_stop);

	CudaCheckError();
	CudaSafeCall(cudaMemcpy((void*) pp_inspects, sd.inspects, num_inst*sizeof(int4), cudaMemcpyDeviceToHost));
	CudaSafeCall(cudaFree(sd_temp.ws));
	CudaSafeCall(cudaFree(sd_temp.vars));
	CudaSafeCall(cudaFree(sd_temp.trail));

	//int int_zero=0;
	//m_CopyToGPU(sd.blocks_complete, &int_zero, sizeof(int));
	
	cudaEventCreate(&kernel_start);
	cudaEventCreate(&kernel_stop);
	cudaEventRecord(kernel_start);



	int kernel_runs;
	
	cudaFuncSetCacheConfig(Solve, CACHE_MODE);
	for (kernel_runs=0; kernel_runs<kernel_runs_limit; kernel_runs++){
		cudaThreadSynchronize ();
		//printf("\n %3i %4i %6i %6i %6.0f", blocksize, num_blocks_truncated, kernel_runs, inspects_limit);

		int (*bcpstat)[BCPSTATSIZE] = (int(*)[BCPSTATSIZE]) malloc(num_inst*sizeof(int)*BCPSTATSIZE);
		int4 h_shards_complete={0,0,0,0};

		CudaSafeCall(cudaStreamCreate(&solver_kernel_stream));
		CudaSafeCall(cudaStreamCreate(&signal_stream));
		Solve <<< num_blocks/DEFAULT_BLOCKSIZE, blocksize, 0, solver_kernel_stream>>> (sd, shadow_reasons, thread_state, employer_transfer_vars, inspects_limit);
		signal(SIGINT, INTHandler);
		int h_stop_flag=0;
		while(1){
			cudaMemcpyFromSymbolAsync(&h_stop_flag, kernel_stop_signal,
						sizeof(int), 0,
						cudaMemcpyDeviceToHost,
						signal_stream);
			if (h_stop_flag==1){
				break;
			}
			if (e_flag==1){
				const int stop_mark=1;
				cudaMemcpyToSymbolAsync(kernel_stop_signal, (void*)
							&stop_mark,
							sizeof(int), 0,
							cudaMemcpyHostToDevice, signal_stream);
				break;
			}
			SleepSomeTime(50000000);
		}
		CudaCheckError();

		CudaSafeCall(cudaStreamDestroy(solver_kernel_stream));
		CudaSafeCall(cudaStreamDestroy(signal_stream));

		CudaSafeCall(cudaMemcpyFromSymbol(&h_shards_complete, shards_complete,
					sizeof(int4), 0,
					cudaMemcpyDeviceToHost));
		
		printf("\n Cycles %i  Complete shards: %i %i %i",
				h_shards_complete.w,
				h_shards_complete.x, h_shards_complete.y, h_shards_complete.z);
		

		int4 h_warps_complete={0,0,0,0};
		CudaSafeCall(cudaMemcpyFromSymbol(&h_warps_complete, warps_complete,
					sizeof(int4), 0,
					cudaMemcpyDeviceToHost));
		printf("\n Warps [comlete, stealings, failed st., total] : %i %i %i %i",
				h_warps_complete.x,
				h_warps_complete.y,
				h_warps_complete.z,
				h_warps_complete.w
				);
		/*
		printf("\n");
		for (int i=0; i<num_inst; i++){
			for (int j=0; j<=bcpstat[i][0]; j++){
				printf("%i ", bcpstat[i][j]);
			}
			printf("\n");
		}
		*/

		//SolveR <<<1, 1>>> (sd, inspects_limit);
		//SolveR <<<1,blocksize>>> (sd, inspects_limit);
		CudaSafeCall(cudaMemcpy((void*) out, sd.out, num_inst*sizeof(RESULT), cudaMemcpyDeviceToHost));

		RESULT batch_state =UNSAT;
		for (int i=0;i<num_inst;i++){
			switch (out[i]){
				case SAT:
					result = SAT;batch_state = SAT;
					break;
				case STOPPED:
					result = STOPPED; batch_state = STOPPED;
				       	//break;
			}
		}
		if (batch_state == UNSAT || batch_state == SAT){
			break;
		}
		free(bcpstat);
	}
	
	cudaThreadSynchronize ();
	cudaEventRecord(kernel_stop);
	cudaEventSynchronize(kernel_stop);
	float solverTime;
	cudaEventElapsedTime(&solverTime, kernel_start, kernel_stop);

	//int*	partial_warps_host=(int*) malloc(WARP_SIZE*sizeof(int));
	//CudaSafeCall(cudaMemcpy((void*) partial_warps_host, partial_warps, WARP_SIZE*sizeof(int), cudaMemcpyDeviceToHost));


	
	/*
	printf("\n Warp sizes counts 0-31:");
	for(int i=0;i<WARP_SIZE;i++)
		printf(" %7i",partial_warps_host[i]);
	printf("\n");
	for(int i=2;i<WARP_SIZE;i++)
		partial_warps_host[i]+=partial_warps_host[i-1];
	int partial_warps_total=partial_warps_host[WARP_SIZE-1];
	int warps_total=partial_warps_host[0];
	printf("\n %i\/%i (%i%%) partial warps",partial_warps_total, warps_total, (partial_warps_total*100)/warps_total);
		
	free(partial_warps_host);
	*/

//	printf("\n Blocksize Blocks  Kernel_runs Inspects_limit  Total_runtime(ms)");
	
	CudaSafeCall(cudaMemcpy((void*) out, sd.out, num_inst*sizeof(RESULT), cudaMemcpyDeviceToHost));
	CudaSafeCall(cudaMemcpy((void*) inspects, sd.inspects, num_inst*sizeof(int4), cudaMemcpyDeviceToHost));

	var_word* output_vars = (var_word*) malloc(num_inst*sizeof(var_word)*s.vars_size);
	CudaSafeCall(cudaMemcpy((void*) output_vars, sd.vars, num_inst*sizeof(var_word)*s.vars_size, cudaMemcpyDeviceToHost));

	
/*
	for(int i=0;i<num_inst;i++)
		cout << "\n" << inspects[i];
*/
	CudaSafeCall(cudaFree(sd.out));
	CudaSafeCall(cudaFree(sd.trail_end));
	CudaSafeCall(cudaFree(sd.BCP_queue_front));
	//CudaSafeCall(cudaFree(sd.BCP_queue_back));
	//CudaSafeCall(cudaFree(sd.BCP_queue));
	CudaSafeCall(cudaFree(sd.decision_var_index));
	CudaSafeCall(cudaFree(sd.inspects));
	CudaSafeCall(cudaFree(sd.ws));
	CudaSafeCall(cudaFree(sd.trail));
	CudaSafeCall(cudaFree(sd.vars));
	//CudaSafeCall(cudaFree(sd.conflict_count_old));

	//CudaSafeCall(cudaFree(sd.bcpstat));

	CudaSafeCall(cudaFree(sd.c.pl));
	CudaSafeCall(cudaFree(sd.c.lits));

	//CudaSafeCall(cudaFree(sd.blocks_complete));

	//CudaSafeCall(cudaFree(partial_warps));

	CudaSafeCall(cudaFree((void*)thread_state));
	CudaSafeCall(cudaFree((void*)employer_transfer_vars));
	int sat=0;
	int stopped=0;
	int unsat=0;
	int satthread=0;
	for(int i=0;i<num_inst;i++){
		if(out[i]==SAT){
			satthread=i;
			sat++;
			for (int m=0; m<c.pl_size/WORD_SIZE+1; m++){
				vars[m]=output_vars[num_inst*m+i];
			}
			
		}else if (out[i]==UNSAT){
			unsat++;
		}else if (out[i]==STOPPED){
			stopped++;
		}
	}
	free(output_vars);

	if(sat>0){
		result=SAT;
	}else if (stopped>0){
		result=STOPPED;
	}else if (unsat==num_inst){
		result=UNSAT;
	}else{
		result=ERROR;
	}

	long long int total_inspects=0;
	long long int pp_total_inspects=0;
	for(int i=0;i<num_inst;i++){
		//if(out[i]==SAT || out[i]==UNSAT){
		{
			printf("\n %6i %7i %7i %7f sh %7i ext %7i", i, inspects[i].x, inspects[i].y,
					100*(float)inspects[i].y/(float)inspects[i].x,
					inspects[i].z, inspects[i].w-inspects[i].z);
		}
		pp_total_inspects+=pp_inspects[i].x;
		total_inspects+=inspects[i].x;
		    if(out[i]==SAT){printf(" S");}
		    if(out[i]==UNSAT){printf(" U");}

	}

	
	printf("\n PP    Stats: %6.2f MIns/sec ",(total_inspects-pp_total_inspects)/1000000/preprocessTime*1000);
	printf("\n Solve Stats: %6.2f MIns/sec ",(total_inspects)/1000000/solverTime*1000);
	printf("\n Results: %3i %5i %6i %6i %9i %6.0f %6.0f  %4i %4i %4i",blocksize, num_blocks,
			kernel_runs, inspects_limit, total_inspects, preprocessTime,
			solverTime, sat, unsat, stopped);
	if (sat>0){
		printf("  sat thread number %5i inspects %i", satthread,
				inspects[satthread].x);
	}
	
/*
	for(int i=0;i<num_inst;i++){
		if(out[i]==SAT){
			cout << "1";
			result = SAT;
		}else{
			if (out[i]==UNSAT)
				cout << "0";
			else
				if (out[i]==STOPPED)
					cout << "P";
				else
					cout << "E";
		}
	}
*/	
	free(out);
	free(inspects);
	free(pp_inspects);
	return result;
}
