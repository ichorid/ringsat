CDF inline bool hasShadow(trailword in){return (bool)(in.var&SEEN_FLAG);};
CDF inline bool isDecision(trailword in){return (bool)(in.var&DECISION_FLAG);};
CDF inline varind getIndex(trailword in){return (varind)((in.var&VARINDEX_MASK)>>1);};
/*
CDF inline varind getIndex(trailword in){
	varind tmp;
	tmp = (varind)((in.var&VARINDEX_MASK)>>1);
	assert (tmp
	return tmp; };
	*/

CDF bool DBGVerifyTrail(SDD)
{
	for (int i=1; i<=trail_end; i++){
		for (int j=1; j<i; j++){
			if (getIndex(trail[stride*i+shard_num])==getIndex(trail[stride*j+shard_num])){
				printf("\n TRAIL (%i) %i %i = %i %i", trail_end, i, getIndex(trail[i]), j, getIndex(trail[j]));
				return true;
			}
		}
	}
	return false;
}


CDF inline int bindex(int b) { return b / WORD_SIZE; }
CDF inline int boffset(int b) { return b & (uint)(WORD_SIZE-1); }
CDF inline void SetBitStrided(SDD,var_word* data, int b) { 
	//atomicOr(&data[stride*bindex(b)+shard_num], 1 << (boffset(b))); 
	data[stride*bindex(b)+shard_num]|= (1 << (boffset(b))); 
}
CDF inline void ClearBitStrided(SDD, var_word* data, int b) { 
	//atomicAnd(&data[stride*bindex(b)+shard_num], ~(1 << (boffset(b))));
	data[stride*bindex(b)+shard_num]&= ~(1 << (boffset(b)));
}
CDF inline bool GetBitStrided(SDD, const var_word* data, int b) { 
	return (bool)(data[stride*bindex(b)+shard_num] & (1 << (boffset(b))));
}
CDF inline  void SetBitSimple(SDD, var_word* data, int b) { 
	//atomicOr(&data[bindex(b)], 1 << (boffset(b))); 
	data[bindex(b)]|= (1 << (boffset(b))); 
}
CDF inline  void ClearBitSimple(SDD, var_word* data, int b) { 
	//atomicAnd(&data[bindex(b)], ~(1 << (boffset(b))));
	data[bindex(b)] &= ~(1 << (boffset(b)));
}
CDF inline bool GetBitSimple(SDD, const var_word* data, int b) { 
	return (bool)(data[bindex(b)] & (1 << (boffset(b))));
}
CDF inline void SetVarset(SDD, int b){
	//assert(b>0);
	//assert(b<c.pl_size/2);
	SetBitStrided(SDA,  vars, b*2);
}
CDF inline void SetVarphase(SDD, int b){
	//assert(b>0);
	//assert(b<c.pl_size/2);
	SetBitStrided(SDA,  vars, b*2+1);
}
CDF inline void ClearVarset(SDD, int b){
	//assert(b>0);
	//assert(b<c.pl_size/2);
	ClearBitStrided(SDA,  vars, b*2);
}
CDF inline void ClearVarphase(SDD, int b){
	//assert(b>0);
	//assert(b<c.pl_size/2);
	ClearBitStrided(SDA,  vars, b*2+1);
}
CDF inline bool GetVarset(SDD,  int b){
	//assert(b>0);
	//assert(b<c.pl_size/2);
	return GetBitStrided(SDA,  vars, b*2);
}
CDF inline bool GetVarphase(SDD, int b)
{
	/*
	assert(b>0);
	assert(b<c.pl_size/2);
	*/
	return GetBitStrided(SDA,  vars, b*2+1);
}

CDF inline void ClearVar(SDD, int b)
{
	//assert(b>0);
	//assert(b<c.pl_size/2);
	//TODO: сделать одной командой!!
	ClearVarphase(SDA,  b);
	ClearVarset(SDA,  b);
	//data[bindex(b*2)] &= ~(3 << (boffset(b*2)));
}

CDF inline int VarToHVar(const varind var){return (var>>1)*(-1+2*(var&1));}
CDF inline varind HVarToVar(const int var)
{
	/*
	assert(var!=0);
	assert (((varind)((abs(var)<<1)|(var<0)))>0);
	*/
	return (varind)((abs(var)<<1)|(var>0));
}

CDF inline bool VarPositive(const varind var){return (bool)(var&1);}

CDF inline int LitToHVar(const Rcnf& c, litind ind){ return VarToHVar(c.lits[ind].y); }

CDF void DBGPrintClauseFromRing(
		const Rcnf& c, 
		litind pos, 
		litind startpos = NO_LITIND, 
		bool top = true)
{
	//assert(pos < c.lits_size);
	if (top){
		startpos = pos;
	}
	printf("t%i:%i ", threadIdx.x, LitToHVar(c, pos));
	if (c.lits[pos].x==startpos){
	//	printf("\n");
	}else{
		DBGPrintClauseFromRing(c, c.lits[pos].x, startpos, false);
	}
}
CDF inline bool isBCPQueueEmpty(SDD)
{
	return (BCP_queue_front>trail_end);
}


CDF bool searchTrail(SDD, const int var)
{
	for (int i=1; i<=trail_end; i++){
		if (getIndex(trail[stride*i+shard_num])==abs(var)){
			return true;
		}
	}
	return false;
}

/*
CDF bool verifytrail(SDD){
	for (int i=1; i<=trail_end; i++){
		for (int j=1; j<i; j++){
			if (getIndex(trail[stride*i+shard_num])==getIndex(trail[stride*j+shard_num])){
				printf("\n trail %i %i", i , j);
				return true;
			}
		}
	}
	return false;
}
*/

CDF bool DBGVerifyVars(SDD){
	for (int i=1; i<=trail_end; i++){
		if (!GetVarset(SDA, getIndex(trail[stride*i+shard_num]))){
			printf("\n No var  trail%i ind%i", i, getIndex(trail[stride*i+shard_num]));
			return true;
		}
	}
	return false;
}

CDF void RemoveWatches(SDD, const litind firstlit)
{
	litind current=0;
	current = firstlit;
	do{
		//ClearBitStrided(SDA, ws, current);
		current=c.lits[current].x;
		//printf("lit %i-%i", current, get_bit(ws,current));
	} while(current != firstlit);
}

CDF inline void BCPQueuePopFront(SDD){BCP_queue_front++;}

CDF inline void BCPQueueClear(SDD){BCP_queue_front=trail_end+1;}

/*
CDF int verifyClauseR(
		SDD,
		TR_ARGS_DEF,
		uint &inspects,
		const Rcnf& c,
		var_word* ws,
		const litind firstlit)
{
	litind current=0;
	current = firstlit;
	int wseen=0;
	//printf("\n");
	do{
		wseen+=GetBitSimple(sd, shard_num, &ws[(c.lits_size/WORD_SIZE+1)*shard_num], current);
		current=c.lits[current].x;
		//printf("lit %i-%i", current, get_bit(ws,current));
	} while(current != firstlit);
	//assert(wseen!=0);
	//assert(wseen!=1);
	//assert(wseen==2);
	return wseen;
}
*/

//TODO: microoptimize!
CDF void SetVar(SDD, const varind ind,
	       	const litind reason_lit = 0, const bool decision_var=false)
{
	//if (shard_num==0 && abs(VarToHVar(ind))==128) printf("\n set var 128 to %i reason %i", ind, reason_lit);
	//if (shard_num==0) printf("\n set var to %i reason %i", ind, reason_lit);
	assert(ind>0);
	assert((ind>>1)<c.pl_size/2);
	assert(!GetVarset(SDA, ind>>1));
	SetVarset(SDA, ind>>1);
	if (VarPositive(ind)){
		SetVarphase(SDA, ind>>1);
	}else{
		ClearVarphase(SDA, ind>>1);
	}
	trailword new_trail_element;
		
	if(decision_var){
		new_trail_element.var=ind |DECISION_FLAG;
		/*
		assert(getIndex(new_trail_element)<c.pl_size/2);
		assert(isDecision(new_trail_element));
		assert(getIndex(new_trail_element)<c.pl_size/2);
		assert(getIndex(new_trail_element)==ind>>1);
		*/
	}else{
		assert(reason_lit>0);
		new_trail_element.var=ind;
	}
	assert(reason_lit>=0);

	assert(getIndex(new_trail_element)<c.pl_size/2);
	assert(reason_lit<c.lits_size);
#ifdef BJ
	new_trail_element.reason=reason_lit;
#endif //BJ
	++trail_end;
	assert(trail_end<c.pl_size/2);
	trail[stride*trail_end+shard_num]=new_trail_element;
}

CDF void SetVarRemove(SDD, const varind ind)
{
	SetVar(SDA, ind);
	/*
	for (int i=c.pl[ind-1]; i<c.pl[ind]; i++){
		if (c.lits[i].x!=NO_LITIND && c.lits[i].y!=0){
			RemoveWatches(SDA, i);
		}
	}
	*/
}

CDF bool DBGPrintClause(SDD, const litind firstlit)
{
	printf("\n");
	litind current_ind = firstlit;

	do{
		assert(c.lits[current_ind].x!=current_ind);
		uintx current_lit = c.lits[current_ind];	
		printf(" %i.%i:(%i|%iw%i)", current_lit.x,
				VarToHVar(current_lit.y),
				GetVarset(SDA,
					current_lit.y>>1),
				GetVarphase(SDA,
					current_lit.y>>1),
				GetBitStrided(SDA, ws,
					current_ind)
				);
		current_ind=c.lits[current_ind].x;
	}while(current_ind!=firstlit);
	return true;
}

CDF bool clauseSolved(SDD, const litind firstlit)
{
	litind next = c.lits[firstlit].x;
	uintx next_lit = c.lits[next];
	while (true){
		litind current = next;
		uintx current_lit=next_lit;
		next = current_lit.x;
		next_lit = c.lits[next];
		uint var_ind = current_lit.y>>1;
		var_word var_container = vars[stride*bindex(var_ind*2)+shard_num];
		bool var_set= (bool)( var_container & (1 << (boffset(var_ind*2))));
		bool var_phase= (bool)(var_container & (1 << (boffset(var_ind*2+1))));
		bool lit_phase = (bool)(current_lit.y&1);
		bool lit_solving = ((var_phase == lit_phase) && var_set);
		if (lit_solving){
			return true;
		}
		if(current==firstlit){
			return false;
		}
	}
}

CDF bool clauseEmpty(SDD, const litind firstlit)
{
	litind next = c.lits[firstlit].x;
	uintx next_lit = c.lits[next];
	while (true){
		litind current = next;
		uintx current_lit=next_lit;
		next = current_lit.x;
		next_lit = c.lits[next];
		uint var_ind = current_lit.y>>1;
		var_word var_container = vars[stride*bindex(var_ind*2)+shard_num];
		bool var_set= (bool)( var_container & (1 << (boffset(var_ind*2))));
		bool var_phase= (bool)(var_container & (1 << (boffset(var_ind*2+1))));
		bool lit_phase = (bool)(current_lit.y&1);
		bool lit_solving = ((var_phase == lit_phase) && var_set);
		if(!var_set){
			return false;
		}
		if (lit_solving){
			return false;
		}
		if(current==firstlit){
			return true;
		}
	}
}

CDF bool clauseUnit(SDD, const litind firstlit)
{
	litind next = c.lits[firstlit].x;
	uintx next_lit = c.lits[next];
	int free_lit_counter=0;
	while (true){
		litind current = next;
		uintx current_lit=next_lit;
		next = current_lit.x;
		next_lit = c.lits[next];
		uint var_ind = current_lit.y>>1;
		var_word var_container = vars[stride*bindex(var_ind*2)+shard_num];
		bool var_set= (bool)( var_container & (1 << (boffset(var_ind*2))));
		bool var_phase= (bool)(var_container & (1 << (boffset(var_ind*2+1))));
		bool lit_phase = (bool)(current_lit.y&1);
		bool lit_solving = ((var_phase == lit_phase) && var_set);
		if (lit_solving){
			return false;
		}
		if (!var_set){
			free_lit_counter++;
		}
		if(current==firstlit){
			break;
		}
	}
	if(free_lit_counter==1){
		return true;
	}
	return false;
}

CDF int CheckClause(SDD, const litind firstlit)
{
	litind ws2_ind=0;
	litind ws1_new=0, ws2_new=0;
	varind ws1_var=0, ws2_var=0;
	assert(firstlit<c.lits_size);
	LIT_STATE ws1_state=NONFREE;
	LIT_STATE ws2_state=UNKNOWN;
	//uint2 current_lit=c.lits[firstlit];

	litind next = c.lits[firstlit].x;
	uintx next_lit = c.lits[next];

	//litind lastlit_ind = firstlit;
	int inspects_local=0;
	//prefetch через двойной буфер по вотчам и фазам только ухудшает
	//производительность
	
	//if (shard_num==3 && firstlit==19266) printf("\n lit.y %i", c.lits[firstlit].y);
	//условия выхода из цикла: кончились литералы или BCP уже точно не будет
	while (true){
		//litind current = current_lit.x;
		litind current = next;
		uintx current_lit=next_lit;
		if(current==firstlit){
			break;
		}
		next = current_lit.x;
		next_lit = c.lits[next];
		//assert(current<c.lits_size);
		inspects_local++;
		inspects.x++;
		//current_lit=c.lits[current];
		// TODO: оптимизировать работу со сдвигами
		uint var_ind = current_lit.y>>1;
		var_word var_container = vars[stride*bindex(var_ind*2)+shard_num];
		//var_word var_container = vars[warpIdx()][bindex(var_ind*2)];
		bool var_set= (bool)( var_container & (1 << (boffset(var_ind*2))));
		bool var_phase= (bool)(var_container & (1 << (boffset(var_ind*2+1))));
		//bool lit_phase = getLitPhase(c,current);
		bool lit_phase = (bool)(current_lit.y&1);
		bool lit_solving = ((var_phase == lit_phase) && var_set);
		bool lit_watched = false;
		// с включением этой оптимизации производительность падает на 10% (((((
		//if(ws2_state==UNKNOWN){
		lit_watched= GetBitStrided(SDA, ws,current);
		//}

		if (lit_watched){
			if (lit_solving){
				inspects.y+=inspects_local;
				return 0;
			}
			ws2_ind=current;
			ws2_var=current_lit.y;
			if (!lit_solving && var_set){
				ws2_state = NONFREE;
			}else{
				ws2_state = FREE;
			}
			continue;
		}

		/*
		if (lit_watched){
			if (lit_solving){
				if (inspects_local>1) inspects.y+=inspects_local;
				//ws1_new=lastlit_ind;
				//ws1_state=SOLVING;
				//break;
				return 0;
			}
			ws2_ind=current;
			ws2_var=current_lit.y;
			if (!lit_solving && var_set){
				ws2_state = NONFREE;
			}else{
				ws2_state = FREE;
			}
			continue;
		}
		*/
		//lastlit_ind = current;

		//литерал выполняет дизъюнкт
		if (lit_solving){
			// поменять первый вотч
		/*	
			if(ws2_state==NONFREE){
				ws2_new=lastlit_ind;
			}
		*/	
			ws1_new=current;
			ws1_var=current_lit.y;
			ws1_state=SOLVING;
			break;
		}
		//литерал несвободен
		if (var_set){
			continue;
		}
		//литерал свободен, второй вотч неизвестен или (известен и свободен)
		//поменять первый вотч
		if (ws1_new==0){
			ws1_new=current;
			ws1_var=current_lit.y;
			if (ws2_state!=NONFREE){
				break;
			}
			continue;
		}
		//литерал свободен, второй вотч известен и несвободен
		if (ws2_state==NONFREE){
			ws2_new=current;
			ws2_var=current_lit.y;
			break;
		}
		/*	
		printf("\n Thread:%i lit %i var %i ws %i vset %i vstate %i",  threadIdx.x, current,
				LitToHVar(c, current),
				GetBitSimple(SDA, shard_num, &ws[(c.lits_size/WORD_SIZE+1)*shard_num],current), var_set, var_phase);
		*/
	}
	//assert(!GetVarset(SDA, shard_num, (c.lits[ws2_ind].y)>>1));
	//assert(((c.lits[ws2_ind].y)>>1)!=((c.lits[firstlit].y)>>1));
	/*
	if (shard_num==3 && firstlit==19266){ printf("\n ws1_new %i ws2_new %i", ws1_new, ws2_new);
			DBGPrintClause(SDA, firstlit);
	}
	*/
	//конфликт либо вывод второго вотча
	if (ws1_new==0 && ws2_new==0){
		if(ws2_state==NONFREE){
			//printf ("\n CONFLICT");
			return ~0;
			//return ws2_ind;
		}else{
			//return ws2_ind;
			return (ws2_var);
			//return ws2_var;
		}
	}
	//если все-таки ворочать вотчи, скорость падает на 2-5%, но уменьшается
	//количество просмотров. бред...
	if (ws2_new){
		SetBitStrided(SDA,
				ws,
				ws2_new);
		ClearBitStrided(SDA,
				ws, 
				ws2_ind);
	}
	//новый первый вотч -> возможный вывод первого вотча
	if (ws1_new){
		SetBitStrided(SDA,
				ws, 
				ws1_new);
		ClearBitStrided(SDA,
				ws, 
				firstlit);
		if(ws1_state==SOLVING){
			inspects.y+=inspects_local;
			return 0;
		}
		if(ws2_new==0 && ws2_state==NONFREE){
			//return ws1_new;
			return (ws1_var);
			//return ws1_var;
		}
	}
	return 0;
}




/*
#ifdef LITCACHE
CDF int CheckClause2(SDD,
		const litind firstlit){
	litind ws2_ind=0;
	litind ws1_new=0, ws2_new=0;
	varind ws1_var=0, ws2_var=0;
	assert(firstlit<c.lits_size);
	LIT_STATE ws1_state=NONFREE;
	LIT_STATE ws2_state=UNKNOWN;
	//uint2 current_lit=c.lits[firstlit];
	

	const uintx cachelit = c.lits[firstlit];
	litind next = cachelit.x;
	//uintx next_lit = c.lits[next];

	litind lastlit_ind = firstlit;
	int inspects_local=0;
	//prefetch через двойной буфер по вотчам и фазам только ухудшает
	//производительность
	
	bool clause_solved=false;
	varind solving_var=0;
	int solving_var_level=c.pl_size/2;
	
	
	//printf("\n %i %i %i %i", cachelit.x ,cachelit.x1,cachelit.x2,cachelit.x3);
	//int litcounter=0;
	//условия выхода из цикла: кончились литералы или BCP уже точно не будет
	//while (true){
	for(int litcounter=1; litcounter<=3; litcounter++){
		//litind current = current_lit.x;
		litind current = next;
		//uintx current_lit=next_lit;

		uint2 current_lit;

		//printf(" |> %i", current_lit.x);

		if(current==firstlit){
			break;
		}
		//next = current_lit.x;
		//next_lit = c.lits[next];


		switch(litcounter){
			case 0:{
				//current_lit.x=next_lit.x;
				//current_lit.y=next_lit.y;
				break;}
			       
			case 1:{
			       	//assert(current_lit.x==cachelit.x1);
			       	//assert(current_lit.y==cachelit.y1);
				current_lit.x=cachelit.x1;
				current_lit.y=cachelit.y1;
				break;}
			case 2:{
			       	//assert(current_lit.x==cachelit.x2);
			       	//assert(current_lit.y==cachelit.y2);
				current_lit.x=cachelit.x2;
				current_lit.y=cachelit.y2;
				break;}
			case 3:{
			       	//assert(current_lit.x==cachelit.x3);
			       	//assert(current_lit.y==cachelit.y3);
				current_lit.x=cachelit.x3;
				current_lit.y=cachelit.y3;
				break;}
		}
		next = current_lit.x;


		//assert(current<c.lits_size);
		inspects_local++;
		inspects.x++;
		//current_lit=c.lits[current];
		// TODO: оптимизировать работу со сдвигами
		uint var_ind = current_lit.y>>1;
		var_word var_container = vars[stride*bindex(var_ind*2)+shard_num];
		//var_word var_container = vars[warpIdx()][bindex(var_ind*2)];
		bool var_set= (bool)( var_container & (1 << (boffset(var_ind*2))));
		bool var_phase= (bool)(var_container & (1 << (boffset(var_ind*2+1))));
		//bool lit_phase = getLitPhase(c,current);
		bool lit_phase = !(bool)(current_lit.y&1);
		bool lit_solving = ((var_phase == lit_phase) && var_set);
		bool lit_watched = false;
		// с включением этой оптимизации производительность падает на 10% (((((
		//if(ws2_state==UNKNOWN){
		lit_watched= GetBitStrided(SDA, ws,current);
		//}

		if (lit_watched){
			if (lit_solving){
				inspects.y+=inspects_local;
				return 0;
			}
			ws2_ind=current;
			ws2_var=current_lit.y;
			if (!lit_solving && var_set){
				ws2_state = NONFREE;
			}else{
				ws2_state = FREE;
			}
			continue;
		}

		//lastlit_ind = current;

		//литерал выполняет дизъюнкт
		if (lit_solving){
			// поменять первый вотч
			ws1_new=current;
			ws1_var=current_lit.y;
			ws1_state=SOLVING;
			break;
		}
		//литерал несвободен
		if (var_set){
			continue;
		}
		//литерал свободен, второй вотч неизвестен или (известен и свободен)
		//поменять первый вотч
		if (ws1_new==0){
			ws1_new=current;
			ws1_var=current_lit.y;
			if (ws2_state!=NONFREE){
				break;
			}
			continue;
		}
		//литерал свободен, второй вотч известен и несвободен
		if (ws2_state==NONFREE){
			ws2_new=current;
			ws2_var=current_lit.y;
			break;
		}
	}
	//assert(!GetVarset(SDA, shard_num, (c.lits[ws2_ind].y)>>1));
	//assert(((c.lits[ws2_ind].y)>>1)!=((c.lits[firstlit].y)>>1));

	//конфликт либо вывод второго вотча
	if (ws1_new==0 && ws2_new==0){
		if(ws2_state==NONFREE){
			//printf ("\n CONFLICT");
			return ~0;
			//return ws2_ind;
		}else{
			//return ws2_ind;
			return (ws2_var);
			//return ws2_var;
		}
	}
	//если все-таки ворочать вотчи, скорость падает на 2-5%, но уменьшается
	//количество просмотров. бред...

	if (ws2_new){
		SetBitStrided(SDA,
				ws,
				ws2_new);
		ClearBitStrided(SDA,
				ws, 
				ws2_ind);
	}
	//новый первый вотч -> возможный вывод первого вотча
	if (ws1_new){
		SetBitStrided(SDA,
				ws, 
				ws1_new);
		ClearBitStrided(SDA,
				ws, 
				firstlit);
		if(ws1_state==SOLVING){
			inspects.y+=inspects_local;
			return 0;
		}
		if(ws2_new==0 && ws2_state==NONFREE){
			//return ws1_new;
			return (ws1_var);
			//return ws1_var;
		}
	}
	return 0;
}
#endif
*/

CDF bool checkVarConflictVars(SDD, int var)
{
	// в очереди стоят только обратные фазы присваеваемых переменых,
	// поэтому их не нужно инвертировать при проверке!
	int ind = abs(var);
	bool phase = var>0;
	
	//assert(ind!=0);
	//assert(ind<c.pl_size/2);
	if (GetVarset(SDA, ind))
	       if (GetVarphase(SDA, ind)!=phase){
		       
			if (threadWidx()==0){
			//	printf("\n1thread %d, var-varset-varphase %i-%i-%i", threadIdx.x, ind, GetVarset(SDA, shard_num, ind), GetVarphase(SDA, shard_num,ind));
			}
			return true;
		}
	return false;
	//return BCP_queue_checkfindR(SDA, shard_num, var);
}




CDF int FindNewRoot(SDD)
{
	for(int i_tp=root_trailpos; i_tp<=trail_end; i_tp++){
		const trailword current_te = trail[stride*i_tp + shard_num];
		if(isDecision(current_te) && !hasShadow(current_te)){
			return i_tp;
		}
	}
	return 0;
}


#ifdef BJ
CDF inline int getReason(trailword in){return in.reason;};

CDF void  DBGPrintTrail(SDD)
{
	printf("\n TRAIL (%i) rtp %i", trail_end, root_trailpos );
	for (int i=1; i<=trail_end; i++){
		//if(isDecision(trail[stride*i+shard_num]))
		printf(" S%i %3i:%3i-%i%i%i-r%i", shard_num, i,
				getIndex(trail[stride*i+shard_num]),
				isDecision(trail[stride*i+shard_num]),
				(int)hasShadow(trail[stride*i+shard_num]),
				trail[stride*i+shard_num].var&1,
				getReason(trail[stride*i+shard_num]));
	}
	printf("\n");
}

CDF int FillReasonBitmapFromLit(SDD, var_word* reason_bitmap, 
		const litind startlit, const varind var=0)
{
	litind current_lit=startlit;
	//if (shard_num==583) DBGPrintClause(SDA, startlit);
	//printf("\n startlit %i", startlit);
	//if (shard_num==583)printf("\n start fill reason bitmap for var %i", c.lits[current_lit].y>>1);
	int count=0;
	do{
	//printf("\n currentlit %i", current_lit);
		if(c.lits[current_lit].y>>1 != var){
			SetBitSimple(SDA, reason_bitmap, c.lits[current_lit].y>>1);
			count++;
			//if (shard_num==583)printf("\n fill reason bitmap  %i", c.lits[current_lit].y>>1);
		}
		current_lit=c.lits[current_lit].x;
	}while(current_lit!=startlit);
	return count;
}

CDF void RestoreReasonFromShadow(SDD, var_word* reason_bitmap,
		const int reason_list_start)
{
	for(int i=reason_list_start; i<shadow_reasons_end; i++){
		assert(reason_list_start<=shadow_reasons_end);
		assert(reason_list_start!=0);
		assert(reason_list_start>0);
		assert(shadow_reasons_end>0);
		assert((shard_num*HIDDEN_REASONS_SIZE+i)>=0);
		const shadowword current = shadow_reasons[shard_num*HIDDEN_REASONS_SIZE+i];
		assert (current<(c.pl_size/2));
		assert (current>0);
		SetBitSimple(SDA, reason_bitmap, current);
	}
}

CDF int StoreReasonToShadow(SDD, var_word* reason_bitmap)
{
	const int reason_list_start = shadow_reasons_end;
	for(int i=0; i<c.pl_size/2; i++){
		if (GetBitSimple(SDA, reason_bitmap, i)){ 
			shadow_reasons[shard_num*HIDDEN_REASONS_SIZE+shadow_reasons_end]=i;
			assert(shadow_reasons_end<HIDDEN_REASONS_SIZE);
			shadow_reasons_end++;
		}
	}
	return reason_list_start;
}

CDF int StoreReasonToShadowFast(SDD, var_word* reason_bitmap,
		const int lits_count)
{
	const int reason_list_start = shadow_reasons_end;
	int lits_found=0;
	for(int i=trail_end; i>0; i--){
		const int current_ind = getIndex(trail[stride*i + shard_num]);
		if (GetBitSimple(SDA, reason_bitmap, current_ind)){ 
			assert(shadow_reasons_end<HIDDEN_REASONS_SIZE);
			if (shadow_reasons_end>=HIDDEN_REASONS_SIZE){
				printf("\n REASONS OVERFLOW shard %i",
						shard_num);
				asm("trap;");
			}
			shadow_reasons[shard_num*HIDDEN_REASONS_SIZE+shadow_reasons_end]=current_ind;
			shadow_reasons_end++;
			lits_found++;
			if(lits_found==lits_count){
				//FIXME неправильно считаем, нужно
				//учитывать и теневые. так что пока
				//считаем все
				//break;
			}
		}
	}
	return reason_list_start;
}

CDF inline int BackjumpFast(SDD, const litind conflict_lit)
{
	var_word reason_bitmap[(VARS_SIZE)/(sizeof(var_word)*8)];
	for (int i=0; i<(VARS_SIZE)/(sizeof(var_word)*8); i++){
		reason_bitmap[i]=0;
		//assert(reason_bitmap[i]==0);
	}
	bool stop_backtrack = false; 
	int lits_count=0;
	lits_count += FillReasonBitmapFromLit(SDA, reason_bitmap, conflict_lit);

	//if (shard_num==583) printf("\n Start BJ");
	// откатываться можно не дальше 1-го родителя !!!!
	int shadow_handle = ~0;
	do{
		trailword current = trail[stride*trail_end+shard_num];
		while (!isDecision(current)){
		// очищаем выведенные переменные
			if (!stop_backtrack){
				if (GetBitSimple(SDA, reason_bitmap, getIndex(current))){
				//if (false){ //BACKTRACKING
					//printf("\n trail end %i", trail_end);
					assert(trail_end>root_trailpos);
					assert(getIndex(current)<c.pl_size/2);
					assert(getReason(current)!=0);
					assert(getReason(current)>0);
					assert(getReason(current)<c.lits_size);
					assert(!isDecision(current));
					assert(getIndex(current)>getIndex(trail[stride*root_trailpos+shard_num]));
					assert(current.reason!=0);
					assert(current.reason!=~0);
					assert(!hasShadow(current));
					
					//if (shard_num==583)printf("\n start fill reason bitmap for var %i", getIndex(current));
					lits_count+= FillReasonBitmapFromLit(SDA,
							reason_bitmap,
							getReason(current),
							getIndex(current));
					lits_count--;
					ClearBitSimple(SDA,
							reason_bitmap,
							getIndex(current));
				}
			}
			//ClearVar(SDA, getIndex(current));
			ClearVarset(SDA, getIndex(current));
			trail_end--;
			current = trail[stride*trail_end+shard_num];
		}
		
		// переключаем переменную уровня решения
		assert(isDecision(current));

		assert(getReason(current)<=HIDDEN_REASONS_SIZE);
		assert(getReason(current)>=0);
		decision_var_index=getIndex(current);
		//if(shard_num==10){ printf("%u ", decision_var_index); }

		
		/*
		if (!hasShadow(current)){
				stop_backtrack=true;
				shadow_handle=1;
		}
		*/
		
		//if (shard_num==583) printf("  %i-%i-%i", decision_var_index, GetBitSimple(SDA, reason_bitmap, decision_var_index), hasShadow(current));
		//if (!GetBitSimple(SDA, reason_bitmap, decision_var_index ) && ((current.var&1)==1)){ printf("\n BACKJUMP");}
		ClearVarset(SDA, decision_var_index);

		trail_end--;
		//дошли до корневой переменной 
		//if (decision_var_index==getIndex(trail[stride*root_trailpos+shard_num])){
		if ((trail_end+1)==root_trailpos){
			stop_backtrack=true;
			 // пытаемся залочить корень 
			 if((atomicCAS((uint*)&thread_state[shard_num],
						 ROOT_READY,
						 ROOT_NOT_READY) ==
					 ROOT_READY)){
				// удалось залочить. Проверяем,
				// требовалось ли откатываться выше
			 	if(hasShadow(current)){
					// требовалось откатиться выше,
					// но уже дошли до корня.
					// Значит, откат невозможен
					shadow_handle=~0;
				}
			 	if(!GetBitSimple(SDA, reason_bitmap, decision_var_index)){
					// переменная не является
					// причиной конфликта и должна
					// быть пропущена.
					// Откат невозможен.
					shadow_handle=~0;
				}
				shadow_handle=0;
			 }else{
				// залочить не удалось. значит откат
				// невозможен
				shadow_handle=~0;
			 }

		}else{
			// если текущая переменная уровня решения является одной
			// из причин конфликта:
			if (GetBitSimple(SDA, reason_bitmap, decision_var_index)){
			//if (true){ // BACKTRACKING
				if(hasShadow(current)){
					// есть тень, то есть уже перещелкивали - восстанавливаем теневые причины
					RestoreReasonFromShadow(SDA, reason_bitmap, getReason(current));
				}else{
					// нет тени, значит нашли самую нижнюю
					// еще не перещелкивавашуюся
					// переменную уровня решения из
					// множества переменных,
					// ответственных за конфликт. Сохраняем
					// текущие теневые причины и заканчиваем
					// откат.
					stop_backtrack=true;
					shadow_handle = StoreReasonToShadowFast(SDA, reason_bitmap, lits_count);
					//shadow_handle = StoreReasonToShadow(SDA, reason_bitmap);
					//shadow_handle = 1; //BACKTRACKING
				}
			}
			// спиливаем уровень в массиве теневых причин так, чтобы
			// он соответствовал текущей переменной уровня решения
			if(hasShadow(current) && !stop_backtrack){
				shadow_reasons_end=getReason(current);
			}
		}
		//повторяем процесс 
	} while (!stop_backtrack);
	BCPQueueClear(SDA);
	return shadow_handle;
}
#endif
/*
CDF inline uint backtracking(SDD, const litind conflict_lit){
	bool backtrack_impossible=false;
	bool stop_backtrack = (GetVarphase(SDA, decision_var_index)==DEFAULT_PHASE);
	do{
		trailword current = trail[stride*trail_end+shard_num];
		// меткой переменной уровня решения является её знак
		while (!isDecision(current)){
			// очищаем выведенные переменные
			ClearVar(SDA, getIndex(current));
			--trail_end;
			current = trail[stride*trail_end+shard_num];
		}
		
		// переключаем переменную уровня решения
		assert(isDecision(current));
		decision_var_index=isDecision(current);

		//перещелкиваем причину
		if (GetVarphase(SDA, decision_var_index)==DEFAULT_PHASE){
			stop_backtrack=true;
		}
		ClearVar(SDA, decision_var_index);

		trail_end--;
		// уже дошли до переменной верхнего уровня, но даже и не собираемся останавливаться
		if ((decision_var_index==top_decision_var_index) && !stop_backtrack){
			stop_backtrack=true;
			backtrack_impossible=true;
		}
		//повторяем процесс 
	} while (!stop_backtrack);
	BCPQueueClear(SDA);
	return (uint)backtrack_impossible;
}
*/

CDF inline int findNextFreeVar(SDD, int var)
{
	while (GetVarset(SDA, abs(var))){
		++var;
		}
	//assert(var<c.pl_size/2);
	return var;
}

CDF void DefineDecisionVar(SDD)
{
	//определение номера новой переменной решения
	//assert(decision_var_index<c.pl_size/2);
	//while(++decision_var_index < c.pl_size/2){
	//	if(!GetVarset(SDA, decision_var_index)){
	for (int i=1; i< c.pl_size/2; i++){
		if(!GetVarset(SDA, vars_heap[stride*i+shard_num])){
			decision_var_index=vars_heap[stride*i+shard_num];
			//__threadfence();
			break;
		}
	}
	//assert(!searchTrail(SDA, shard_num, decision_var_index));
	/*
	if ((int)decision_var_index>= (int)c.pl_size/2){
		printf("\n var_index / pl_size/2 :   %i / %i",decision_var_index , c.pl_size/2);
	}
	assert(decision_var_index<c.pl_size/2);
	*/
}
