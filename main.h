#include <iostream>
#include <fstream>
#include <cassert>
#include <vector>
#include <stack>
#include <deque>
#include <string>
#include <sstream>
#include <algorithm>
#include <ctime>
#include <string.h>
#include <math.h>

#define BCP_ARGS BCP_queue, BCP_queue_back, BCP_queue_front
#define BCP_ARGS_DEF varind* BCP_queue, int &BCP_queue_back, int &BCP_queue_front
#define DEFAULT_PHASE true

#define LITS_ALIGNMENT 128
using namespace std;
class IStream
{
	std::istream& in;
	char c;
public:
	IStream(std::istream& s = std::cin): in(s), c(0){in.get(c);}
	char operator * () {return c;}
	void operator ++ () {in.get(c);}
	bool eof() const {return in.eof();}
};



static inline double cpuTime(void) { return (double)clock() / CLOCKS_PER_SEC; }

