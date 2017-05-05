#define NDEBUG
#define BCP_QUEUE_SIZE 800
#define BCPSTATSIZE 5000
#define DEFAULT_PHASE true
#define DEFAULT_INSPECTS 50000
//#define DEFAULT_INSPECTS 500000
#define DECISIONS_LIMIT 5000000
#define DEFAULT_CYCLES 500000000
#define DEFAULT_KERNEL_RUNS 1
#define VARS_SIZE 10000
//typedef int trailword;
#define BJ
typedef unsigned short shadowword;
typedef int varind;
typedef struct {
	uint var;
#ifdef BJ
	int reason;
#endif
} trailword;
typedef struct {
	double start;
	int level_count;
	double average;
	double last;
	double sum;
} lstats;

typedef unsigned int uint;
#define NO_LITIND  0xffffffff
#define END_LITIND 0xfffffffe
#define SEEN_FLAG 0x40000000
#define DECISION_FLAG 0x80000000
#define VARINDEX_MASK 0x0fffffff
typedef unsigned int litind;
struct uintx {
	uint x;
	uint y;
	
#ifdef LITCACHE
	uint x1;
	uint y1;
	uint x2;
	uint y2;
	uint x3;
	uint y3;
#endif
	/*
	uint z;
	uint w;
	uint a;
	uint b;
	uint c;
	uint d;
	uint e;
	uint f;
	uint g;
	uint h;
	uint l;
	uint k;
	uint m;
	uint n;
	
	
	uint x1;
	uint y1;
	uint z1;
	uint w1;
	uint a1;
	uint b1;
	uint c1;
	uint d1;
	uint e1;
	uint f1;
	uint g1;
	uint h1;
	uint l1;
	uint k1;
	uint m1;
	uint n1;
*/	
};
typedef struct {
	int x;
	int y;
} litind2;
//typedef unsigned int varcont;
typedef bool varcont;
typedef bool wscont;
typedef uint  var_word;
typedef enum {SAT, UNSAT, CONFLICT, ERROR, OK, STOPPED, FORCED_DECISION, DEFAULT_DECISION, BCP_OK, BCP_STALL} RESULT;
typedef enum {BACKTRACKING=0, BACKJUMPING=1, BACKJUMPING_FAST=2} CONFLICT_RESOLUTION_METHOD;
typedef enum {FREE=1, NONFREE=2, SOLVING=4,  PENDING=16, UNKNOWN=0} LIT_STATE;
enum { WORD_SIZE = sizeof(var_word) * 8 };
struct Rlit{
	litind nextlit;
	litind var;
};

struct Rcnf{
	uintx* lits; // 
	litind* pl; // номера окончания фаз
	int lits_size;
	int pl_size;
	//int vote_threshold;
};

struct Rsolverstate{
//	var_word* vars;
//	varcont* var_set;//массив состояния переменных - присвоенность
//	varcont* var_phase;//массив состояния переменных - фаза
	int vars_size;
	int model_size;
//	var_word* ws;//состояние watched literals
//	int* trail; //последовательность присвоенных переменных
	int trail_end;
	int ws_size;
	double propagations;
	uint bogus_bcp;
	uint bogus_bcp_sat;
	int vars_set;
	int decision_var_index;
	int top_decision_var_index;
	int levels_size;
	int var_index;
	int BCP_queue_front;
	double stat_inspects_last;
	double stat_inspects;
	double stat_inspects_bogus;
	double stat_inspects_single;
};
struct gpusolverdata{
	gpusolverdata(): c(), trail(NULL), trail_end(NULL), decision_var_index(NULL), ws(NULL), vars(NULL), out(NULL), inspects(NULL){}
	Rcnf c;
	trailword* trail;
	int* trail_end;
	int* decision_var_index;
	int* top_decision_var_index;
	var_word* ws; 
	var_word* vars; 
	RESULT* out;
	int4* inspects;
	int multi;
	int stride;
	int* blocks_complete;
	varind (*BCP_queue)[BCP_QUEUE_SIZE];
	int *BCP_queue_front, *BCP_queue_back;
	int *conflict_count_old;
	int *stall_count;
	int (*bcpstat)[BCPSTATSIZE];
	varind* vars_heap;
};

RESULT SolverSolve(
		Rcnf &c,
		Rsolverstate &s,
		var_word* vars,
		var_word* ws,
		trailword* trail,
		int multi,
		int inspects_limit =DEFAULT_INSPECTS,
		int kernel_runs_limit =DEFAULT_KERNEL_RUNS,
		bool truncate =false,
		const int subproblem=0);

