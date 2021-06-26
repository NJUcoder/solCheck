#include "CFG.h"
#include "BasicBlock.h"
#include "global.h"
//! VarType : INT => INT_, BOOL => BOOL_

//static int tranID = 0;
//! stateID use NodeID
//static int stateID = 0; 
Variable* newIntVariable(string name, unsigned numbits, int& varID) {//generate INT/INTNUM variable
	VarType type = isNumerical(name) ? INTNUM : INTMACRO;
	Variable* a = new Variable(name, varID, type, numbits);
	varID++;
	return a;
}


map<Operator, string> ops;
map<Op_m, string> op_ms;
string getOp_mStr(Op_m op) {
	switch (op)
	{
	case TRUNC: return "TRUNC";
	case ZEXT: return "ZEXT";
	case ADD: return "+";
	case SUB:return "-";
	case MUL:return "*";
	case UDIV:return "/(u)";
	case SDIV:return "/(s)";
	case UREM:return "%(u)";
	case SREM:return "%(s)";
	case LSHR:return ">>(u)";
	case ASHR:return ">>(s)";
	case SHL:return "<<";
	case AND:return "&&";
	case OR:return "||";
	case XOR:return "^";
	case POW:return "**";
	case eq:return "==";
	case slt:return "<(s)";
	case sle:return "<=(s)";
	case sgt:return ">(s)";
	case sge:return ">=(s)";
	case ult:return "<(u)";
	case ule:return "<=(u)";
	case ugt:return ">(u)";
	case uge:return ">=(u)";
	case NONE: return "NONE";
	default:return to_string(op);
	}
}
Op_m getParaOp(string op) {
	if (op == "add") return ADD;
	else if (op == "mul") return MUL;
	else if (op == "sub")return SUB;
	else if (op == "div")return UDIV;
	else if (op == "sdiv")return SDIV;
	else if (op == "mod")return UREM;
	else if (op == "smod")return SREM;
	else if (op == "zext")return ZEXT;
	else if (op == "truncate")return TRUNC;
	else if (op == "exp")return POW;//TODO: need to verify
	else if (op == "lt") return ult;
	else if (op == "gt")return ugt;
	else if (op == "slt")return slt;
	else if (op == "sgt")return sgt;
	else if (op == "eq") return eq;
	else if (op == "and")return AND;
	else if (op == "or")return OR;
	else if (op == "xor")return XOR;
	else if (op == "not") return NONE;//TODO: not to transform to other operator
	else if (op == "shl")return SHL;
	else if (op == "shr") return LSHR;
	else if (op == "sar")return ASHR;
	else return NONE;
}

string getOpStr(Operator op) {
	switch (op)
	{
	case ASSIGN:return "=";
	case ULT:return "<";
	case UGT:return ">";
	case EQ:return "==";
	case NE:return "!=";
	default:return to_string(op);
	}
}
Operator getOp(LeftOp lop) {
	switch (lop) {
	case LeftOp::ASSIGNMENT:return ASSIGN;
	case LeftOp::LESS:return ULT;
	case LeftOp::GREATER:return UGT;
	case LeftOp::EQUAL:return EQ;
	case LeftOp::NOT_EQUAL:return NE;
	default:
		cout << "wrong left operator" << endl;
		exit(-1);
	}
}
//buildContractCFG only initial stateList and transitionList
void printVariable(const Variable* v) {
	cout << v->name;
}
void printParaVariable(const ParaVariable pv) {
	if (pv.lvar != NULL) {
		printVariable(pv.lvar);
		cout << " " << getOp_mStr(pv.op) << " ";
	}
	printVariable(pv.rvar);
}

void printConstraint(const Constraint& c) {
	printParaVariable(c.lpvList);
	cout << " " << getOpStr(c.op) << " ";
	printParaVariable(c.rpvList);
}
void testCFG(CFG* cfg) {
	for (auto s : cfg->stateList) {
		if (s.isInitial)cout << "[INITIAL]";
		cout << "name : " << s.name << ", label : " << s.label << endl;
		for (auto c : s.consList) {
			cout << "\t"; printConstraint(c); cout << endl;
		}
	}
	for (auto t : cfg->transitionList) {
		cout << "[Transition]tran_id : " << t.ID << ", name : " << t.name << ", fromName : " << t.fromName <<
			", toName : " << t.toName << ", fromLabel : " << t.fromLabel << ", toLabel : " << t.toLabel << endl;
		for (auto c : t.guardList) {
			cout << "\t"; printConstraint(c); cout << endl;
		}
	}
}
void buildContractCFG(CFG* cfg, map<int, ECFGNode>& nodes) {
	int varID = 0;
	map<string, Variable* > variable;
	map<string, State*> stateNameMap;

	for (auto& node : nodes) {
		State state;
		if (node.first == 0)
			state.isInitial = true;
		state.name = "s" + to_string(node.first);//name represents NodeID
		state.label = "s_" + to_string(node.first);//indicates control flow information

		cfg->stateList.push_back(state);
	}
	for (int i = 0; i < cfg->stateList.size(); i++)
		stateNameMap[cfg->stateList[i].name] = &cfg->stateList[i];

	map<string, Constraint> condCons;
	for (auto& node : nodes) {
		int ID = node.second.getID();
		int fallsID = node.second.getFallsID();
		int jumpID = node.second.getJumpID();
		string jumpName, fallName;
		if (jumpID != -1) {
			Transition jump("s" + to_string(ID), "s" + to_string(jumpID));
			jump.name = "e" + to_string(ID) + "_" + to_string(jumpID);
			jump.fromLabel = "s_" + to_string(ID);
			jump.toLabel = "s_" + to_string(jumpID);

			jumpName = jump.name;
			cfg->transitionList.push_back(jump);
		}
		if (fallsID != -1) {
			Transition fall("s" + to_string(ID), "s" + to_string(fallsID));
			fall.name = "e" + to_string(ID) + "_" + to_string(fallsID);
			fall.fromLabel = "s_" + to_string(ID);
			fall.toLabel = "s_" + to_string(fallsID);

			fallName = fall.name;
			cfg->transitionList.push_back(fall);
		}
		if (fallsID != -1 && jumpID != -1) {//! only JUMPI needs to add constraints
			string condVar = node.second.getEndTopStr() + "#" + to_string(node.second.getEndTopIdx());
			string zero = "0";
			if (variable.find(condVar) == variable.end()) {
				variable[condVar] = newIntVariable(condVar, 256, varID);//stack elements' size is always 256
			}
			ParaVariable lpvList(false, NULL, variable[condVar], NONE);
			if (variable.find(zero) == variable.end()) {
				variable[zero] = newIntVariable(zero, 256, varID);
			}
			ParaVariable rpvList(false, NULL, variable[zero], NONE);

			Constraint jumpCond, fallCond;
			jumpCond.lpvList = fallCond.lpvList = lpvList;
			jumpCond.rpvList = fallCond.rpvList = rpvList;
			jumpCond.op = NE;
			fallCond.op = EQ;

			condCons[jumpName] = jumpCond;
			condCons[fallName] = fallCond;
		}
	}

	for (auto& con : condCons)
		for (auto& t : cfg->transitionList)
			if (t.name == con.first)
				t.guardList.push_back(con.second);

	for (auto& node : nodes) {//generate Variables from instr expr
		State* state = stateNameMap["s" + to_string(node.first)];

		for (auto& exprs : node.second.getExprs()) {
			for (auto& expr : exprs.second) {
				//if (expr.isRedundant())
				//	continue;
				Operand left = expr.getLeftOperand();
				string value = left.getStr();
				if (variable.find(value) == variable.end()) {
					variable[value] = newIntVariable(value, left.getBits(), varID);
				}
				ParaVariable lpvList(false, NULL, variable[value], NONE);
				vector<Operand> right = expr.getRightOperand();
				for (auto& r : right) {
					string value = r.getStr();
					if (variable.find(value) == variable.end()) {
						variable[value] = newIntVariable(value, r.getBits(), varID);
					}
				}

				ParaVariable rpvList;
				//! currently assume right.size() == 1 or 2
				if (expr.getRightOperand().size() == 1) {
					rpvList = ParaVariable(false, NULL, variable[right[0].getStr()], NONE);
				}
				else {
					rpvList = ParaVariable(true, variable[right[0].getStr()], variable[right[1].getStr()], getParaOp(expr.getOp()));
				}
				Constraint c;
				c.lpvList = lpvList;
				c.rpvList = rpvList;
				c.op = getOp(expr.getLeftOp());

				state->InsertConstraint(c);
			}
		}
		//generate Variables from phi assignments at the end of the block
		//! it's necesary to do that because the phi function may be dead and generate new variable name
		for (auto& expr : node.second.getPhiAssign()) {
			Operand left = expr.getLeftOperand();
			string value = left.getStr();
			if (variable.find(value) == variable.end()) {
				variable[value] = newIntVariable(value, left.getBits(), varID);
			}
			ParaVariable lpvList(false, NULL, variable[value], NONE);
			vector<Operand> right = expr.getRightOperand();
			for (auto& r : right) {
				string value = r.getStr();
				if (variable.find(value) == variable.end()) {
					variable[value] = newIntVariable(value, r.getBits(), varID);
				}
			}
			ParaVariable rpvList;
			//! currently assume right.size() == 1 or 2
			if (expr.getRightOperand().size() == 1) {
				rpvList = ParaVariable(false, NULL, variable[right[0].getStr()], NONE);
			}
			else {
				rpvList = ParaVariable(true, variable[right[0].getStr()], variable[right[1].getStr()], getParaOp(expr.getOp()));
			}
			Constraint c;
			c.lpvList = lpvList;
			c.rpvList = rpvList;
			c.op = getOp(expr.getLeftOp());

			state->InsertConstraint(c);
		}
	}
}
void generateCFG(map<int, ECFGNode>& nodes) {
	map<string, Variable* > variable;
	map<int, State* >stateMap;
	map<int, Transition* > transitionMap;
	map<string, State*>stateStrMap;
	map<string, Transition*> transitionStrMap;
	int stateID = 0;
	int tranID = 0;
	int varID = 0;
	map<int, int> IDMap;//NodeID => state ID
	for (auto& node : nodes) {
		State* state = new State();
		if (node.first == 0)
			state->isInitial = true;
		state->ID = stateID; stateID++;

		state->name = "s" + to_string(node.first);//name represents NodeID
		//state->label = "State_" + to_string(node.first);
		state->label = to_string(node.first);//indicates control flow information

		IDMap[node.first] = state->ID;
		stateMap[state->ID] = state;
		stateStrMap[state->name] = state;
	}

	tranID = stateID;
	for (auto& node : nodes) {
		int ID = node.second.getID();//node.first
		int fallsID = node.second.getFallsID();
		int jumpID = node.second.getJumpID();
		Transition* jump, * fall;
		jump = fall = NULL;
		int cfgID = IDMap[ID];
		if (jumpID != -1) {
			int cfgJumpID = IDMap[jumpID];
			jump = new Transition(stateMap[cfgID]->name, stateMap[cfgJumpID]->name);//here Transition::ID has been assigned
			//jump->name = "transition_" + to_string(jump->ID);
			jump->name = "e" + to_string(jump->ID);
			jump->ID = tranID; tranID++;
			jump->fromState = stateMap[cfgID];
			jump->toState = stateMap[cfgJumpID];
			jump->fromLabel = stateMap[cfgID]->label;
			jump->toLabel = stateMap[cfgJumpID]->label;

			stateMap[cfgID]->InsertTransition(jump);

			transitionMap[jump->ID] = jump;
			transitionStrMap[jump->name] = jump;
		}
		if (fallsID != -1) {
			int cfgFallsID = IDMap[fallsID];

			fall = new Transition(stateMap[cfgID]->name, stateMap[cfgFallsID]->name);
			fall->name = "e" + to_string(fall->ID);//here fall->ID is independent transition id
			fall->ID = tranID; tranID++;//here ID is global ID
			fall->fromState = stateMap[cfgID];
			fall->toState = stateMap[cfgFallsID];
			fall->fromLabel = stateMap[cfgID]->label;
			fall->toLabel = stateMap[cfgFallsID]->label;

			stateMap[cfgID]->InsertTransition(fall);
			transitionMap[fall->ID] = fall;
			transitionStrMap[fall->name] = fall;
		}
		if (fallsID != -1 && jumpID != -1) {//! only JUMPI needs to add constraints
			string condVar = node.second.getEndTopStr() + "#" + to_string(node.second.getEndTopIdx());
			string zero = "0";
			if (variable.find(condVar) == variable.end()) {
				variable[condVar] = newIntVariable(condVar, 256, varID);//stack elements' size is always 256
			}
			ParaVariable lpvList(false, NULL, variable[condVar], NONE);
			if (variable.find(zero) == variable.end()) {
				variable[zero] = newIntVariable(zero, 256, varID);
			}
			ParaVariable rpvList(false, NULL, variable[zero], NONE);

			Constraint jumpCond, fallCond;
			jumpCond.lpvList = fallCond.lpvList = lpvList;
			jumpCond.rpvList = fallCond.rpvList = rpvList;
			jumpCond.op = NE;
			fallCond.op = EQ;
			jump->guardList.push_back(jumpCond);
			fall->guardList.push_back(fallCond);
		}
	}
	for (auto& node : nodes) {//generate Variables from instr expr
		State* state = stateMap[IDMap[node.first]];

		for (auto& exprs : node.second.getExprs()) {
			for (auto& expr : exprs.second) {
				if (expr.isRedundant())
					continue;
				Operand left = expr.getLeftOperand();
				string value = left.getStr();
				if (variable.find(value) == variable.end()) {
					variable[value] = newIntVariable(value, left.getBits(), varID);
				}
				ParaVariable lpvList(false, NULL, variable[value], NONE);
				vector<Operand> right = expr.getRightOperand();
				for (auto& r : right) {
					string value = r.getStr();
					if (variable.find(value) == variable.end()) {
						variable[value] = newIntVariable(value, r.getBits(), varID);
					}
				}

				ParaVariable rpvList;
				//! currently assume right.size() == 1 or 2
				if (expr.getRightOperand().size() == 1) {
					rpvList = ParaVariable(false, NULL, variable[right[0].getStr()], NONE);
				}
				else {
					rpvList = ParaVariable(true, variable[right[0].getStr()], variable[right[1].getStr()], getParaOp(expr.getOp()));
				}
				Constraint c;
				c.lpvList = lpvList;
				c.rpvList = rpvList;
				c.op = getOp(expr.getLeftOp());

				state->InsertConstraint(c);
			}
		}
		//generate Variables from phi assignments at the end of the block
		//! it's necesary to do that because the phi function may be dead and generate new variable name
		for (auto& expr : node.second.getPhiAssign()) {
			Operand left = expr.getLeftOperand();
			string value = left.getStr();
			if (variable.find(value) == variable.end()) {
				variable[value] = newIntVariable(value, left.getBits(), varID);
			}
			ParaVariable lpvList(false, NULL, variable[value], NONE);
			vector<Operand> right = expr.getRightOperand();
			for (auto& r : right) {
				string value = r.getStr();
				if (variable.find(value) == variable.end()) {
					variable[value] = newIntVariable(value, r.getBits(), varID);
				}
			}
			ParaVariable rpvList;
			//! currently assume right.size() == 1 or 2
			if (expr.getRightOperand().size() == 1) {
				rpvList = ParaVariable(false, NULL, variable[right[0].getStr()], NONE);
			}
			else {
				rpvList = ParaVariable(true, variable[right[0].getStr()], variable[right[1].getStr()], getParaOp(expr.getOp()));
			}
			Constraint c;
			c.lpvList = lpvList;
			c.rpvList = rpvList;
			c.op = getOp(expr.getLeftOp());

			state->InsertConstraint(c);
		}
	}


}