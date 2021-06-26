//#pragma once
// Define the CFG's Data Structure
#ifndef  _CFG_H___
#define  _CFG_H___
#include <iostream>
#include <string>
#include <vector> 
#include <list>
#include <fstream>
#include <map>
#include <stdlib.h> 
#include <assert.h>
//#include "llvm/IR/BasicBlock.h"
//#include "llvm/Analysis/CFG.h"
//#include "llvm/Analysis/CallGraph.h"
//#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/Debug.h"
//#include "llvm/IR/Module.h" 
//#include "convinent.h"
#include "assert.h"
//#include "general.h"
#ifdef _WIN32
#include "c++/z3++.h"//new
#endif
#ifdef __linux__
#include "z3++.h"
#endif
//#include "z3++.h"

enum Operator {
	ASSIGN,
	EQ, NE,
	SLT, SLE, SGT, SGE,
	ULT, ULE, UGT, UGE,
	FEQ, FNE,
	FLT, FLE, FGT, FGE,
};
enum Op_m {
	TRUNC, ZEXT, SEXT, FPTRUNC, FPEXT, FPTOUI, FPTOSI, UITOFP, SITOFP,
	FADD, ADD, SUB, FSUB, MUL, FMUL, UDIV, SDIV, FDIV,
	UREM, SREM, FREM,
	LSHR, ASHR, SHL, AND, NAND, OR, XOR,
	ABS, FABS,
	ISNAN, ISINF, ISNORMAL, ISFINITE, SIGNBIT, CLASSIFY, //SETROUND,
	SINH, COSH, TANH, TAN, ATAN, ATAN2, SIN, ASIN, COS, ACOS, SQRT, POW, LOG, LOG10, EXP,
	ADDR, GETPTR, STORE, LOAD, ALLOCA, BITCAST,
	eq, ne,
	slt, sle, sgt, sge,
	ult, ule, ugt, uge,
	feq, fne,
	flt, fle, fgt, fge,
	NONE,
};

enum Err {
	Noerr,
	Assert,
	Spec,
	Div0,
	DomainLog,
	DomainSqrt,
	DomainTri
};

extern Operator getEnumOperator(std::string str);
extern Op_m get_m_Operator(std::string str);
extern std::string get_m_Operator_str(Op_m op);
//extern llvm::raw_ostream& operator << (llvm::raw_ostream& os, Operator& object);
//extern llvm::raw_ostream& operator << (llvm::raw_ostream& os, Op_m& object);
//extern llvm::raw_ostream& operator << (llvm::raw_ostream& os, Err& object);
std::string intToString(int value);

#ifdef _WIN32
#define INTMACRO INT_      //The var store a INT type data
#endif
#ifdef __linux__
#define INTMACRO INT
#endif

#ifdef _WIN32
#define BOOLMACRO BOOL_
#endif
#ifdef __linux__
#define BOOLMACRO BOOL
#endif

// variable type
enum VarType {
	//INT,
	INTNUM,     //The var is a INT num
	FPNUM,      //The var is a FP num
	INTMACRO,	//The var store a INT type data
	FP,         //The var store a FP type data
	// FP32,    //The var store a 32bit-FP type data
	// FP64,    //The var store a 64bit-FP type data
	PTR,        //The var store a ID of a PTR var
	BOOLMACRO	//The var store a BOOL type data
};

class Variable {
public:
	VarType type;
	std::string name;
	int ID;
	unsigned numbits;

	// Constructor
	Variable() { type = FP; ID = -1; numbits = 0; }
	Variable(std::string name1, int id, VarType ty, unsigned nb) { name = name1; ID = id; type = ty; numbits = nb; }
	Variable(const Variable& a) {
		this->name = a.name;
		this->ID = a.ID;
		this->type = a.type;
		this->numbits = a.numbits;
	}
	Variable(const Variable* a) {
		this->name = a->name;
		this->ID = a->ID;
		this->type = a->type;
		this->numbits = a->numbits;
	}

	//void print() { llvm::errs() << "name=" << name << ";id=" << ID; }
	void print() { std::cout << "name=" << name << ";id=" << ID; }//new
	void printName();
	std::string getName();
	double getVal();
	Variable& operator =(const Variable& a) {
		this->name = a.name;
		this->ID = a.ID;
		this->type = a.type;
		this->numbits = a.numbits;
		return *this;
	}
	//friend llvm::raw_ostream& operator << (llvm::raw_ostream& os, Variable& object);
};

class ParaVariable {
public:
	bool isExp;     // is an expression
	Op_m op;
	Variable* lvar;
	Variable* rvar;
	std::vector<Variable*> varList;

	// Constructor
	ParaVariable() { isExp = false; lvar = NULL; rvar = NULL; op = NONE; }
	ParaVariable(bool iE, Variable* lv, Variable* rv, Op_m opr) {
		isExp = iE;
		lvar = lv;
		rvar = rv;
		op = opr;
	}
	ParaVariable(const ParaVariable& a) {
		this->isExp = a.isExp;
		this->lvar = a.lvar;
		this->rvar = a.rvar;
		this->op = a.op;
		this->varList = a.varList;
	}

	// Destructor
	~ParaVariable() { isExp = false; lvar = NULL; rvar = NULL; op = NONE; varList.clear(); }

	ParaVariable& operator =(const ParaVariable& a) {
		this->isExp = a.isExp;
		this->lvar = a.lvar;
		this->rvar = a.rvar;
		this->op = a.op;
		this->varList = a.varList;
		return *this;
	}

	void print() {
		if (lvar != NULL)
			lvar->print();
		std::cout << op;
		rvar->print();
		for (unsigned i = 0; i < varList.size(); i++)
			std::cout << varList[i] << ", ";
		std::cout << "\n";
	}

	//friend llvm::raw_ostream & operator << (llvm::raw_ostream & os, ParaVariable & object);
};

class Constraint {
public:
	ParaVariable lpvList;
	ParaVariable rpvList;
	Operator op;

	Constraint() {};
	~Constraint() {};

	Constraint& operator =(const Constraint& a) {
		this->lpvList = a.lpvList;
		this->rpvList = a.rpvList;
		this->op = a.op;
		return *this;
	}

	//friend llvm::raw_ostream& operator << (llvm::raw_ostream& os, Constraint& object);
};


class Transition;
class State {
public:
	bool isInitial;
	int ID;
	std::string funcName;
	int nextS;
	std::string name;
	std::string label;
	int level;
	Err error;
	std::vector<Transition*> transList;     // transitions List (Edge)
	std::vector<Constraint> consList;        // assignments List
	std::string ContentRec;                  // location in the file
	std::vector<int> locList;                // line number of the code

	// Constructor
	State() {
		this->level = -1;
		this->ID = 0;
		this->name = "";
		this->funcName = "";
		this->isInitial = false;
		this->label = "";
		nextS = -1;
		error = Noerr;
	}
	State(int id, std::string name, std::string funcName) {
		this->level = -1;
		this->ID = id;
		this->name = name;
		this->funcName = funcName;
		this->isInitial = false;
		this->label = "";
		nextS = -1;
		error = Noerr;
	}
	State(bool bo, int id, std::string name1, std::string funcName1) {
		isInitial = bo;
		ID = id;
		name = name1;
		funcName = funcName1;
		nextS = -1;
		level = -1;
		error = Noerr;
		this->label = "";
	}
	State(bool bo, int id, std::string name1, std::string funcName1, std::string label) {
		isInitial = bo;
		ID = id;
		name = name1;
		funcName = funcName1;
		nextS = -1;
		level = -1;
		error = Noerr;
		this->label = label;
	}

	void InsertTransition(Transition* tr) { this->transList.push_back(tr); }
	void InsertConstraint(Constraint cons) { this->consList.push_back(cons); }

	State& operator =(const State& a) {
		this->isInitial = a.isInitial;
		this->ID = a.ID;
		this->name = a.name;
		this->funcName = a.funcName;
		this->label = a.label;
		this->nextS = a.nextS;
		this->transList = a.transList;
		this->ContentRec = a.ContentRec;
		this->consList = a.consList;
		this->locList = a.locList;
		this->level = a.level;
		this->error = a.error;
		return *this;
	}

	//friend llvm::raw_ostream& operator << (llvm::raw_ostream& os, State object);
};

class Transition {
public:
	int ID;
	static int tran_id;
	std::string name;
	State* fromState;
	State* toState;
	std::string fromName;
	std::string fromLabel;
	std::string toName;
	std::string toLabel;
	int level;
	std::vector<Constraint> guardList;
	bool creatrByPhi = false;         // whether the transition is created by phi node        

	// Constructor
	Transition(int id, std::string name1) : ID(id), name(name1) { fromLabel = ""; toLabel = ""; level = -1; }
	Transition(std::string fromName, std::string toName) {
		this->fromName = fromName;
		this->toName = toName;
		this->ID = tran_id++;
		this->level = -1;
	}

	Transition& operator =(const Transition& a) {
		this->ID = a.ID;
		this->tran_id = a.tran_id;
		this->name = a.name;
		this->fromName = a.fromName;
		this->toName = a.toName;
		this->fromState = a.fromState;
		this->toState = a.toState;
		this->fromLabel = a.fromLabel;
		this->toLabel = a.toLabel;
		this->guardList = a.guardList;
		this->level = a.level;
		return *this;
	}

	//friend llvm::raw_ostream& operator << (llvm::raw_ostream& os, Transition object);
};

class CFG {
private:
	std::map<int, State*> stateMap;
	std::map<int, Transition*> transitionMap;
	std::map<std::string, State*> stateStrMap;
	std::map<std::string, Transition*> transitionStrMap;
	std::map<int, std::string> nameMap;
	bool linear;
	bool modeLock;

public:
	std::map<std::string, State*> LabelMap;
	std::map<std::string, int> funcTime;
	std::map<std::string, std::string> endBlock;
	std::vector<std::string> retVar;
	std::list<ParaVariable> callVar;
	std::list<Constraint> initialCons;

	std::string name;
	std::string startFunc;
	unsigned counter_state;
	unsigned counter_s_state;
	unsigned counter_q_state;
	unsigned counter_variable;
	unsigned counter_transition;
	State* initialState;
	std::vector<State> stateList;
	// at the same time  ,equals to the transList
	std::vector<Transition> transitionList;
	std::vector<Variable> variableList;
	std::vector<Variable> exprList;
	std::vector<unsigned> mainInput;

	// use both to map mainInputID to expr, z3::expr do not support map as its container
	std::vector<int> mainInputID;
	std::vector<z3::expr> mainInputExpr;
	std::vector<std::pair<unsigned, unsigned>> mainInputLocation;

	Constraint c_tmp1;
	Constraint c_tmp2;

	CFG() {
		counter_state = 0;
		counter_variable = 0;
		counter_s_state = 0;
		counter_q_state = 0;
		counter_transition = 0;
		linear = true;
		modeLock = false;
	}

	void print();
	void printLinearMode();
	bool initial();
	bool is_state(const unsigned ID);
	bool isLinear();
	void setModeLock();
	void setLinear();
	void setUnlinear();
	bool hasVariable(std::string name);
	Variable* getVariable(std::string name);

	void InsertCFGState(int id, std::string name, std::string funcName);
	void InsertCFGTransition(Transition* tr);

	State* getState(int id) { return &stateList[id]; }
	State* getLabelState(std::string Label) {
		std::map<std::string, State*>::iterator l_it = LabelMap.find(Label);
		if (l_it == LabelMap.end())
			return NULL;
		else
			return l_it->second;
	}
	Variable* getVariable(const int varID);
	std::string getNodeName(int i);
	void removeDuplicatedStates();

	// Search function
	State* searchState(int stateID);
	State* searchState(std::string name);
	Transition* searchTransition(std::string name);
	Transition* searchTransition(int transID);
	Transition* searchTransitionByState(int from, int to);
	Transition* searchTransitionByLabel(std::string from, std::string to);

	CFG& operator =(const CFG& a) {
		this->name = a.name;
		this->initialState = a.initialState;
		this->stateList = a.stateList;
		this->transitionList = a.transitionList;
		this->variableList = a.variableList;
		this->counter_state = a.counter_state;
		this->counter_variable = a.counter_variable;
		this->counter_s_state = a.counter_s_state;
		this->counter_q_state = a.counter_q_state;
		this->counter_transition = a.counter_transition;
		return *this;
	};

};

extern CFG global_CFG;

class IndexPair {
public:
	int start;
	int end;
	IndexPair(int _start, int _end) : start(_start), end(_end) {}
	bool contain(IndexPair& index) { return start >= index.start && end <= index.end; }
	void print() { std::cout << "(" << start << "," << end << ")"; }
};

class Verify {
public:
	Verify() {};
	virtual ~Verify() {};
	virtual bool check(CFG* ha, std::vector<int>& path) = 0;
	virtual std::vector<IndexPair> get_core_index() = 0;
	virtual double getTime() = 0;
	virtual void print_sol(CFG* cfg) = 0;
	virtual bool isResultUnknown() = 0;
	virtual void resetUnknown() = 0;
};

void printPath(CFG* cfg, std::vector<int> path);

#endif