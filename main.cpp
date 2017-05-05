#include <cuda_types.h>
#include <main.h>
#include <solver.h>
#define INDEX_MASK 0xffffff
#define INDEX_SHIFT 24

inline int VarToHVar(const varind var){return (var>>1)*(-1+2*(var&1));}
inline bool VarPositive(const varind var){return (bool)(var&1);}
inline varind HVar2Var(const int var){ return (varind)((abs(var)<<1)|(var>0)); }

inline bool isSeen(trailword in){return (bool)(in.var&SEEN_FLAG);};
inline bool isDecision(trailword in){return (bool)(in.var&DECISION_FLAG);};
inline varind getIndex(trailword in){return (varind)((in.var&VARINDEX_MASK)>>1);};
int decisions_limit=DECISIONS_LIMIT;
int inspects_limit=DEFAULT_INSPECTS;
CONFLICT_RESOLUTION_METHOD conflict_resolution_method = BACKTRACKING;

const uint2 test[3] = {{1,2}, {3,4}, {5,6}};

bool compare_lits_num(int lit1, int lit2){
	//делаешь в прямом - получается в обратном. Потому что потом
	//через стек прогоняется.
	return (lit1>lit2);
}
bool compare_clauses_size(vector <int> cl1, vector <int> cl2){
	return (cl1.size()<cl2.size());
}

void printUsage(char** argv){
	cout << "USAGE: " << argv[0] << " <input-file> [decisions limit] [conflict resolution method]" << endl;
}

void verifyRing(const Rcnf &c, const litind firstlit){
	litind current=firstlit;
	int lits_in_clause=0;
	do{
		assert(lits_in_clause++<1000);
		current=c.lits[current].x;
	} while(current != firstlit);
}
void skipLine(IStream& in){
	while(in.eof() || *in != '\n') ++in;
	if(*in == '\n') ++in;
}
bool match(IStream& in, const char *str){
	for (; *str != 0; ++str, ++in)
	if (*str != *in)
		return false;
	return true;
}
void skipWhitespace(IStream& in){
	while ((*in >= 9 && *in <= 13) || *in == 32){
        ++in; 
		if(in.eof()) return;
	}
}

int parseInt(IStream& in){
	int     val = 0;
	bool    neg = false;
	skipWhitespace(in);
	if      (*in == '-') neg = true, ++in;
	else if (*in == '+') ++in;
	if (*in < '0' || *in > '9') cout << "PARSE ERROR! Unexpected char:" << *in << endl, exit(1);
	while (*in >= '0' && *in <= '9')
		val = val*10 + (*in - '0'),
		++in;
	return neg ? -val : val;
}

inline int bindex(int b) { return b / WORD_SIZE; }
inline int boffset(int b) { return b % WORD_SIZE; }

inline void set_bit(var_word* data, int b) { 
	data[bindex(b)] |= 1 << (boffset(b)); 
}
inline void clear_bit(var_word* data, int b) { 
	data[bindex(b)] &= ~(1 << (boffset(b)));
}
inline bool get_bit(const var_word* data, int b) { 
	return (bool)(data[bindex(b)] & (1 << (boffset(b))));
}

inline void set_varset(var_word* data, int b){
	set_bit(data, b*2);
}
inline void set_varphase(var_word* data, int b){
	set_bit(data, b*2+1);
}

inline void clear_varset(var_word* data, int b){
	clear_bit(data, b*2);
}
inline void clear_varphase(var_word* data, int b){
	clear_bit(data, b*2+1);
}
inline bool get_varset(const var_word* data, int b){
	return get_bit(data, b*2);
}
inline bool get_varphase(const var_word* data, int b){
	return get_bit(data, b*2+1);
}
void DebugPrintTrail(const trailword* trail, const int &trail_end){
	cout <<"Trail "<< trail_end<<":";
	for (int i=0; i<= trail_end;i++){
		cout  << getIndex(trail[i]) << " ";
	}
}

void readClauseR(Rcnf &c, litind* cpl_tmp, vector< vector<int> > &clauses, stack <int> &unitclauses, int &lits_shift, IStream& in){
	uint lit;
	int lastlit;
	vector<int> clause;
	uint lits_count = 0;
	bool phase = true;
	int lits_shift_tmp =0; 
	for(;;){
		int var = parseInt(in);
		if(var == 0) break;
		lits_count++;
		phase = (var > 0);
		lastlit = var;
		// делаем из номера переменной и фазы литерал,
		// соответствующий способу нумерации в основном
		// массиве: 
		lit  = HVar2Var(var);
		clause.push_back(lit);
		//увеличиваем счетчики литералов
		assert(lit<VARS_SIZE*2);
		++cpl_tmp[lit];
		//считаем разницу между числом положительных и
		//отрицательных литералов КНФ
		//lits_shift_tmp += 1 - 2*(int)phase;
	}
	if (lits_count > 1){
		clauses.push_back(clause);
		c.lits_size += lits_count;
		lits_shift += lits_shift_tmp;
	}
	if (lits_count == 1){
		unitclauses.push(lastlit);
		//отматываем счетчик литералов, если литерал был только один
		--cpl_tmp[lit];
//		cout << "UC:" << unitclauses.top() << "\n";
	}
}

void PrintStats(Rsolverstate &s){
	if (s.propagations > 0){
		cout << "\n c Propagations: " << s.propagations;
		cout << "\n c bogus props: " << s.bogus_bcp << " " << ((float)s.bogus_bcp*100)/s.propagations << "%";
		cout << "\n c bogus sat props: " << s.bogus_bcp_sat << " " << ((float)s.bogus_bcp_sat*100)/s.propagations << "%";
		cout << "\n c bogus literal inspects: " << s.stat_inspects_bogus << " " << ((float)s.stat_inspects_bogus*100)/s.stat_inspects << "%";
		cout << "\n c single literal inspects: " << s.stat_inspects_single << " " << ((float)s.stat_inspects_single*100)/s.stat_inspects_bogus << "%";
		cout << "\n c unneeded literal inspects: " << s.stat_inspects_bogus-s.stat_inspects_single << " " << ((float)(s.stat_inspects_bogus-s.stat_inspects_single)*100)/s.stat_inspects_bogus<< "% (of bogus) " << ((float)(s.stat_inspects_bogus-s.stat_inspects_single)*100)/s.stat_inspects<< "% (of all)" ;
		cout <<"\n";
	}
}

void DropStats(Rsolverstate &s){
	s.propagations = 0;
	s.bogus_bcp = 0;
	s.bogus_bcp_sat = 0;
	s.stat_inspects_bogus=0;
	s.stat_inspects=0;
	s.stat_inspects_single=0;
}
inline int LitToHVar(const Rcnf& c, litind ind){
	/*
	if (ind > c.lits_size/2){
		// + фаза
		return c.lits[ind].y ;
	}else{
		return  -c.lits[ind].y;
	}
	*/
	if ((bool)(c.lits[ind].y&1)){
		// + фаза
		return (c.lits[ind].y>>1) ;
	}else{
		return  -(c.lits[ind].y>>1);
	}
}

/*
inline uint  LitToRVar(const Rcnf& c, litind n){
	int var;
	if (n > c.lits_size/2){
		// + фаза
		var = c.lits[n].y+c.pl_size/2;
	}else{
		var = c.lits[n].y;
	}
	return (var);
}
*/

//inline int getReason(trailword in){return in.reason};
bool verifytrail(trailword* trail,
	       	int &trail_end){
	for (int i=1; i<=trail_end; i++){
		for (int j=1; j<i; j++){
			if (getIndex(trail[i])==getIndex(trail[j])){
				printf("\n TRAIL (%i) %i %i = %i %i", trail_end, i, getIndex(trail[i]), j, getIndex(trail[j]));
				return true;
			}
		}
	}
	return false;
}

bool searchtrail(trailword* trail,
	       	int &trail_end,
		int var){
	for (int i=1; i<=trail_end; i++){
		if (getIndex(trail[i])==abs(var)){
			return true;
		}
	}
	return false;
}

litind insertLit(Rcnf& c, litind pos, litind value){
			// проверяем состояние последней ячейки под
			// литерал в базе литералов
			if (c.lits[pos].x==NO_LITIND){
				c.lits[pos].x = value;
				return pos;
			}
			else{
				//рекурсивный вызов - ищем дальше
				//свободную ячейку
				return insertLit(c, pos+1, value);
				//return pos;
			}
}

/*
void PrintClauseFromRing(const Rcnf& c, litind pos, litind startpos = NO_LITIND, bool top = true){
	assert(pos < c.lits_size);
	if (top){
		startpos = pos;
	}
	cout << LitToHVar(c, pos) << " ";
	if (c.lits[pos].x==startpos){
		cout << "0\n" ;
	}else{
		PrintClauseFromRing(c, c.lits[pos].x, startpos, false);
	}
}
*/

//TODO: вставлять вотчи одновременно с созданием дизъюнктов

int InsertWatchInClauseRing(const Rcnf& c, var_word *ws, litind pos, litind startpos = NO_LITIND, bool top = true){
	assert(pos < c.lits_size);
	if (top){
		startpos = pos;
	}
	if (get_bit(ws,pos)){
		return 2;
	}
	if (c.lits[pos].x==startpos){
		assert(pos!=startpos);
		set_bit(ws,pos);
		return 1;
	}
	if (InsertWatchInClauseRing(c, ws, c.lits[pos].x, startpos, false)<2){
		set_bit(ws,pos);
		return 2;
	}else{
		return 2;
	}
}

void DeleteClauseFromRing(Rcnf& c, litind pos){
	litind nextlit = c.lits[pos].x;
	if (nextlit!=NO_LITIND){
		c.lits[pos].x=NO_LITIND;
		DeleteClauseFromRing(c, nextlit);
	}
}


litind getPreviousLit(Rcnf& c, litind pos, litind startpos = NO_LITIND){
	if (startpos == NO_LITIND){
		startpos = pos;
	}
	if (c.lits[pos].x!=startpos){
		getPreviousLit(c, c.lits[pos].x, startpos);

	}
		return pos;
}
/*
inline uint invertRVar(const Rsolverstate &s, uint ind){
	if(ind > s.model_size/2){
		return ind-s.model_size/2;
	}else{
		return ind+s.model_size/2;
	}
}
*/
void SetVar(var_word* vars, trailword* trail, int &trail_end,  const uint &decision_var_index, int ind, const litind reason_lit = 0){
	/*
	assert(ind>0);
	assert(!GPU_get_varset(GPU_SD_ARGS, ind>>1));
	*/
	set_varset(vars, ind>>1);
	if (VarPositive(ind)){
		set_varphase(vars, ind>>1);
	}else{
		clear_varphase(vars, ind>>1);
	}
	trailword new_trail_element;
		
	if(decision_var_index==(ind>>1)){
		new_trail_element.var=ind |DECISION_FLAG;
		//(DECISION_FLAG*(int)(decision_var_index==(ind>>1)));
		/*
		assert(getIndex(new_trail_element)<c.pl_size/2);
		assert(isDecision(new_trail_element));
		assert(getIndex(new_trail_element)<c.pl_size/2);
		assert(getIndex(new_trail_element)==ind>>1);
		*/
	}else{
		new_trail_element.var=ind;
	}
#ifdef BJ
	new_trail_element.reason=reason_lit;
	//FIXME: Еще костыль! надо чтобы не зависела от порядка
	//переменных!
	/*
	if (decision_var_index<top_decision_var_index){
		new_trail_element.reason=0;
	}
	*/
#endif
	++trail_end;
	//trail[stride*trail_end+shard_num].var=(varind)((ind>>1)*(1-2*(int)(decision_var_index==abs(ind>>1))));
	trail[trail_end]=new_trail_element;
}
#ifdef LITCACHE
void InsertLitCache(Rcnf& c, const int firstlit){
		//Индусский код, добавляем кэш литералов!
		uint2 lit[4];
		int litpos[4];
		int j=0;
		uintx currentlit=c.lits[firstlit];
		litind prevpos=firstlit;
		do{
			c.lits[prevpos].x2=END_LITIND;
			c.lits[prevpos].y2=END_LITIND;
			c.lits[prevpos].x3=END_LITIND;
			c.lits[prevpos].x3=END_LITIND;
			litpos[j]=prevpos;
			lit[j].x=currentlit.x;
			lit[j].y=currentlit.y;
			j++;
			prevpos=currentlit.x;
			currentlit=c.lits[currentlit.x];
		}while (c.lits[firstlit].x!=currentlit.x);
		assert(j<=4);
		switch (j){
			case 2:{
				c.lits[litpos[0]].x1=lit[1].x;
				c.lits[litpos[0]].y1=lit[1].y;

				c.lits[litpos[1]].x1=lit[0].x;
				c.lits[litpos[1]].y1=lit[0].y;
				break;}
			case 3:{
				c.lits[litpos[0]].x1=lit[1].x;
				c.lits[litpos[0]].y1=lit[1].y;
				c.lits[litpos[0]].x2=lit[2].x;
				c.lits[litpos[0]].y2=lit[2].y;

				c.lits[litpos[1]].x1=lit[2].x;
				c.lits[litpos[1]].y1=lit[2].y;
				c.lits[litpos[1]].x2=lit[0].x;
				c.lits[litpos[1]].y2=lit[0].y;

				c.lits[litpos[2]].x1=lit[0].x;
				c.lits[litpos[2]].y1=lit[0].y;
				c.lits[litpos[2]].x2=lit[1].x;
				c.lits[litpos[2]].y2=lit[1].y;
				break;}
			case 4:{
				c.lits[litpos[0]].x1=lit[1].x;
				c.lits[litpos[0]].y1=lit[1].y;
				c.lits[litpos[0]].x2=lit[2].x;
				c.lits[litpos[0]].y2=lit[2].y;
				c.lits[litpos[0]].x3=lit[3].x;
				c.lits[litpos[0]].y3=lit[3].y;

				c.lits[litpos[1]].x1=lit[2].x;
				c.lits[litpos[1]].y1=lit[2].y;
				c.lits[litpos[1]].x2=lit[3].x;
				c.lits[litpos[1]].y2=lit[3].y;
				c.lits[litpos[1]].x3=lit[0].x;
				c.lits[litpos[1]].y3=lit[0].y;

				c.lits[litpos[2]].x1=lit[3].x;
				c.lits[litpos[2]].y1=lit[3].y;
				c.lits[litpos[2]].x2=lit[0].x;
				c.lits[litpos[2]].y2=lit[0].y;
				c.lits[litpos[2]].x3=lit[1].x;
				c.lits[litpos[2]].y3=lit[1].y;

				c.lits[litpos[3]].x1=lit[0].x;
				c.lits[litpos[3]].y1=lit[0].y;
				c.lits[litpos[3]].x2=lit[1].x;
				c.lits[litpos[3]].y2=lit[1].y;
				c.lits[litpos[3]].x3=lit[2].x;
				c.lits[litpos[3]].y3=lit[2].y;
				break;}
		}
}
#endif
	

void ReadDimacsToRcnf(Rcnf& c, stack <int> &unitclauses, const char* file_name){
	vector< vector<int> > clauses;
	stack <int> empty;
	int lits_shift=0;
	c.lits_size = 0;
	c.pl_size = 0;

	double starttime=cpuTime();
	ifstream file(file_name, ios::in);

	if(!file.is_open()){
		cout << "File " << file_name << " not found!" << endl;
		exit(1);
	}
	IStream in(file);
	litind* cpl_tmp = (litind*) calloc(VARS_SIZE*2, sizeof(litind));
	for(;;){
		skipWhitespace(in);
		if(in.eof()) break;
		//заголовок DIMACS-файла
		else if((*in == 'p') && match(in, "p cnf")){
			skipLine(in);
		}
		//пропускаем комментарии
		else
		       	if(*in == 'c')
			skipLine(in);
		else
			readClauseR(c,cpl_tmp,clauses,unitclauses,lits_shift,in);
	}
	file.close();

	printf("\nFile read time: %.2f", cpuTime() - starttime);

	// ищем последний ненулевой элемент в невыронянном массиве длин
	// фаз - определяем будущий размер следа
	for(int i=VARS_SIZE*2-1;i>1;i--){
		if (cpl_tmp[i]>0){
			c.pl_size=i+1;
			break;
		}
	}
	//TODO: оптимизировать копирование/создание конечного массива pl
	c.pl = (litind*) calloc(c.pl_size, sizeof(litind));
	for (int i=0; i<c.pl_size; i++){
		c.pl[i]=cpl_tmp[i];
	}
	free(cpl_tmp);
	assert(c.pl_size>=6);

	
	cout << "\nc lits size w/o alignment:" << c.lits_size ;
	//первый элемент "+"-фазы  = 1, т.к. 0-переменная имеет 1 негативный литерал
	c.pl[0]=1;
	c.pl[1]=1;
	//c.pl[c.pl_size/2]=c.lits_size/2+1;
	//c.pl[c.pl_size/2]=1;
	for (int i=0; i<c.pl_size; i++){
		// выравнивание 
		int orig = c.pl[i];
		//printf("\n %i %i", i, orig);
		//if (c.pl[i]==0) c.pl[i]=1;
		assert(c.pl[i]>0);
		c.pl[i] = ((sizeof(uintx)*c.pl[i]+(LITS_ALIGNMENT-(sizeof(uintx)*c.pl[i])%LITS_ALIGNMENT)))/sizeof(uintx);
		assert(((c.pl[i]*sizeof(uintx))%LITS_ALIGNMENT==0) && (c.pl[i]>=orig));
	}
	for (int i=1; i<c.pl_size; i++){
		//превращаем счетчики литералов в номера окончания
		//литералов фаз. К каждому
		//значению прибавляем значения всех предыдущих.
		c.pl[i] += c.pl[i-1];
	}
	c.lits_size = c.pl[c.pl_size-1]; 
	cout << "\nc lits size + align:" << c.lits_size;
	printf("\n");
	for (int i=0;i<c.pl_size;i++){
		if(c.pl[i]>c.lits_size)
			printf (" %i", c.pl[i]);
		assert(c.pl[i]<=c.lits_size);
	}

	starttime = cpuTime();
	// создаем основной массив 
	//cout << s.nl_size << "\n";
	c.lits = (uintx*) malloc(c.lits_size*sizeof(uintx));
	if (c.lits == NULL) exit (1);
	for (int i=0; i<c.lits_size; i++){
		c.lits[i].x = NO_LITIND;
		c.lits[i].y = 0;
	}

	// Заполняем массив соответствия литералов переменным
	for (litind i=1; i<c.pl_size; i++){
		for (litind j=c.pl[i-1]; j<c.pl[i]; j++){
			/*
			if(i < c.pl_size/2){
				c.lits[j].y = i;
			}else{
				c.lits[j].y = i - c.pl_size/2;
			}
			*/
			c.lits[j].y=i;
			//cout << "\n j: " << j;
			//c.lits[j].var = i;
		}
	}
	/*	
	for (litind i=0; i<c.lits_size; i++){
		cout << "\n" << c.lits[i].var;
	}
	*/	
	printf("\n array creation time: %.2f", cpuTime() - starttime);
	//сортировка на simd-вариант не влияет
		stable_sort(clauses.begin(),clauses.end(),compare_clauses_size);
	// переносим дизъюнкты в основной массив из вспомогательного:
	// проходим по дизъюнктам во вспомогательном массиве
	for (int i=0; i<clauses.size(); i++){
		int pv;
		int pos_prev=0;
		int pos_first;
		// обрабатываем первый литерал. 0 - временная ссылка
		stable_sort(clauses[i].begin(),clauses[i].end(),compare_lits_num);
		pv = clauses[i].back();
		clauses[i].pop_back();
		//cout << "vars.end[pv] " << s.vars_end[pv] << "\n";
		pos_first = insertLit(c, c.pl[pv-1], pos_prev);
		//cout << "pos_prev " << pos_prev << " pv " << pv << " vars_end[pv] "<< s.vars_end[pv]<< " shift (pv-1) " << s.vars_end[pv-1] << "\n";
		pos_prev = pos_first;
		//TODO:переписать в функционально-рекурсивном стиле
		//проходим по всем литералам дизъюнкта
		while (clauses[i].size()>0){
			pv = clauses[i].back(); // текущий литерал
			clauses[i].pop_back(); // текущий литерал
			pos_prev = insertLit(c, c.pl[pv-1], pos_prev);
			//cout << LitToVar(s, pos_prev) << "\n";
			//cout << "pos_prev " << pos_prev << " pv " << pv << " shift (pv-1) " << s.vars_end[pv-1] << "\n";
		}
		// записываем в первый литерал ссылку на последний
		c.lits[pos_first].x=pos_prev;
		//verifyRing(c,pos_first);

#ifdef LITCACHE
		InsertLitCache(c, pos_first);
#endif
	}
}

void DebugPrintVars(var_word* vars,const uint model_size){
	for (litind i=0; i<model_size; i++){
		if (get_varset(vars,i)){
			cout <<"\n "<<(int)i*(-1+2*get_varphase(vars,i))<<" 0";;
		}
	}
}

void DebugPrintRingSolver(const Rcnf &c){
	cout << "\n";
	for (int i=0; i<c.lits_size; i++){
		cout << c.lits[i].x << " ";
	}
}
/*
void PrintCnfFromRingSolver(Rcnf &c){
	//проходим по всем записям в массиве литералов
	cout << "p cnf " << c.pl_size/2-1 << " 1\n";
	for (int i=1; i<c.lits_size; i++){
		//переходим к обходу кольца
		// если попался уже осмотренный литерал - идем дальше.
		// так избегаем повторов при обходе всего массива
		// литералов
		if (c.lits[i].x != NO_LITIND){
			PrintClauseFromRing(c, getPreviousLit(c, c.lits[i].x));
			DeleteClauseFromRing(c, c.lits[i].x);
		}
	}
}
*/



inline void BCP_queue_clearR(BCP_ARGS_DEF){
	BCP_queue_front=1;
	BCP_queue_back=0;
}
/*
inline litind varH2PL(const Rcnf &c, int var){
	if(var >0){
		return var+c.pl_size/2;
	}else{
		return abs(var);
	}
}
*/

int InsertWatchInClauseRingDumb (const Rcnf& c, Rsolverstate &s, var_word* ws, const litind firstlit){
	litind current=0,  last=0;
	current = firstlit;
	int wseen=0;
	int lits_in_clause=0;
	do{
		wseen+=get_bit(ws,current);
		last=current;
		current=c.lits[current].x;
		//assert(lits_in_clause++<1000);
		//printf("\n %i | %i %i     %i", firstlit,  c.lits[current].x, c.lits[current].y, current);
		if (lits_in_clause++>100){
			assert (false);

		}
	} while(current != firstlit);
	assert(wseen!=1);
	if(wseen==0){
		set_bit(ws,current);
		set_bit(ws,last);
		return 2;
	}
	return wseen;
}


void verifyClauseR(const Rcnf& c, Rsolverstate &s, var_word* vars, var_word* ws, const litind firstlit){
	litind current=0;
	current = firstlit;
	int wseen=0;
//	printf("\n");
	do{
		wseen+=get_bit(ws,current);
		current=c.lits[current].x;
//		printf("lit %i-%i", current, get_bit(ws,current));
	} while(current != firstlit);
	assert(wseen!=0);
	assert(wseen!=1);
	assert(wseen==2);
}




void ConstructRsolverstate(const Rcnf &c, Rsolverstate &s, var_word*
		&vars, var_word* &ws, trailword* &trail){
	s.model_size = c.pl_size/2;
	s.vars_size = s.model_size*2/WORD_SIZE+1;
	vars = (var_word*) malloc(s.vars_size*sizeof(var_word));
	if (vars == NULL) exit (1);
	for (int i=0;i<s.model_size; i++){
			clear_varset(vars,i);
			clear_varphase(vars,i);
	}
	s.ws_size = c.lits_size/WORD_SIZE+1;
	ws = (var_word*) malloc(s.ws_size*sizeof(var_word));
	if (ws == NULL) exit (1);
	for (int i=0;i<s.ws_size; i++){
		ws[i] = 0;
	}
	int j=0;
	for (int i=1;i<c.lits_size; i++){
		if (c.lits[i].x!=NO_LITIND && c.lits[i].x!=0){
			j+=InsertWatchInClauseRingDumb(c, s, ws, i);
		}
	}
	for (int i=1;i<c.lits_size; i++){
		if (c.lits[i].x!=NO_LITIND && c.lits[i].x!=0){
			verifyClauseR(c, s, vars, ws, i);
		}
	}
	s.decision_var_index=0;
	s.trail_end=0;
	trail = (trailword*) malloc(s.model_size*sizeof(trailword));
	if (trail== NULL) exit (1);
	trail[0].var=0;
	// очищаем очередь переменных
	s.BCP_queue_front=s.trail_end+1;

	s.propagations = 0;
	s.bogus_bcp = 0;
	s.bogus_bcp_sat = 0;
	s.vars_set = 0;
	s.stat_inspects_bogus=0;
	s.stat_inspects=0;
	s.stat_inspects_single=0;

}

void DeconstructRsolverstate(Rsolverstate &s, var_word* vars, var_word* ws, trailword* trail){
	free(trail);
	free(vars);
	free(ws);
}



bool Preprocess(Rcnf &c, Rsolverstate &s, var_word* vars, var_word*
		ws, trailword* trail, stack <int> &unitclauses){
	while (unitclauses.size() > 0){
		//TODO: предупреждения о повторах и конфликтах
		if(get_varset(vars, abs(unitclauses.top()))){
			if(get_varphase(vars, abs(unitclauses.top()))==(unitclauses.top()>0)){
				unitclauses.pop();
				continue;
			}else{
				printf("\n ERROR, UC conflict!");
				assert(false);
			}
		}
		SetVar(vars, trail, s.trail_end,  s.decision_var_index, HVar2Var(unitclauses.top()));
	}
//	DebugPrintVarsR(s);
	return true;
	
}
void ToplevelSolve(const char* file_name, int multi){
	RESULT result = ERROR;
	var_word *vars, *ws;
	trailword *trail;
	Rcnf c;
	Rsolverstate s;
	stack <int> unitclauses;
	ReadDimacsToRcnf(c, unitclauses, file_name);

	ConstructRsolverstate(c, s, vars, ws, trail);
	Preprocess(c, s, vars, ws, trail, unitclauses);

	assert(!verifytrail(trail, s.trail_end));
	printf("\n TRAILEND %i",s.trail_end);
	
	/*
	for (int i=0; i<c.pl_size/2;i++){
		printf("\n tv_cpu %i %i", i, getIndex(trail[i]));
	}
	*/
		assert(!verifytrail(trail, s.trail_end));
	if (SolverSolve(c ,s, vars, ws, trail, multi, inspects_limit)==SAT){
		cout << "\n!!!  SAT  !!!\n";
		DebugPrintVars(vars, s.model_size);cout << "\n";
	}else{
		cout << "\n!!! UNSAT !!!\n";
	}
	
	/*
	var_word* vars_tmp = (var_word*) malloc(c.pl_size/2*2*sizeof(var_word));
	memcpy(vars_tmp, vars, sizeof(var_word)*s[0].vars_size);
	for (int i=0; i<2^10; i++){
		memcpy(vars, vars_tmp, sizeof(var_word)*s[0].vars_size);
		c.vote_threshold=i;
		if (ToplevelGPUSolveR(c,s,vars,ws,trail,
					multi,DEFAULT_BLOCKSIZE,
					DEFAULT_INSPECTS,
					DEFAULT_KERNEL_RUNS,false, i)==SAT){
			//	cout << "\n!!!  SAT  !!!\n";
			DebugPrintVarsR(vars,s[0].model_size);cout << "\n";
		}else{
			//	cout << "\n!!! UNSAT !!!\n";
		}
	}
	free(vars_tmp);
	*/
	
	printf("\n");
	PrintStats(s);
	free(c.lits);
	free(c.pl);
	DeconstructRsolverstate(s,vars,ws,trail);
}
int main(int argc, char* argv[]){
	int multi=0;
	
	if(argc < 2){
		printUsage(argv);
		exit(1);
	}else{
		if (argc > 2){
			multi=atoi(argv[2]);
		}
		if (argc > 3){
			inspects_limit=atoi(argv[3]);
		}
		if (argc > 4){
			//conflict_resolution_method=atoi(argv[4]);
			if (atoi(argv[4])==0){
				conflict_resolution_method=BACKTRACKING;
				}
			if (atoi(argv[4])==1){
				conflict_resolution_method=BACKJUMPING;
				}
			if (atoi(argv[4])==2){
				conflict_resolution_method=BACKJUMPING_FAST;
				}
		}
	}


	ToplevelSolve(argv[1],multi);
}
