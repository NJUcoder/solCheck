#pragma once
#pragma once
#include <string>
#include <map>
#include <vector>
#include <set>
#include <iostream>

#include "Expr.h"
#ifdef _WIN32
#include "c++/z3++.h"
#endif
#ifdef __linux__
#include "z3++.h"
#endif
using namespace std;
enum class BlockType {
	/*0	*/NODEFINE,
	/*1	*/JUMP,
	/*2	*/JUMPI,
	/*3	*/CREATE,
	/*4	*/MESSAGECALL,//call/callcode/delegatecall/staticcall
	/*5	*/INVALID,
	/*6	*/NATURAL,//physically
	/*7	*/REVERT,
	/*8	*/RETURN,
	/*9	*/STOP,
	/*10	*/SELFDESTRUCT
};
class EBasicBlock {
private:
	int start;
	int end;
	map<int, string> instrs;
	BlockType jumpType;//falls jumpi jump (revert/invalid) (call/callcode/delegatecall/staticcall) (return/stop) 
public:
	EBasicBlock(int start, int end, BlockType jumpType, map<int, string> instrs) :start(start), end(end), instrs(instrs), jumpType(jumpType) {}

	void setStart(int start) { this->start = start; }
	int getStart() const { return start; }

	void setEnd(int end) { this->end = end; }
	int getEnd() const { return end; }

	void setInstrs(map<int, string> instrs) { this->instrs = instrs; }
	const map<int, string>& getInstrs() const { return instrs; }

	void setJumpType(BlockType jumpType) { this->jumpType = jumpType; }
	const BlockType& getJumpType() const { return jumpType; }
};
class ECFGNode {
private:
	int ID;
	const EBasicBlock* node;
	set<int> parents;//parents ID(start block's parent is -1)

	vector<int> jumpInfo;
	//string jumpIn;//用以标识该基本块的是否是经过函数调用的基本信息
	int jumpAddr;
	int fallsAddr;

	int jumpID;//CFG Jump Node ID
	int fallsID;//CFG natural Node ID
	static int count;

	//! member "exprs" is not handled in constructor and copy constructor function
	//不过不重要，因为一般在构建完CFG后不会在进行CFGNode的拷贝复制
	map<int, vector<Expr>> exprs;

	int endTop;// stack top after symbolic execution : mu_S_endTop#-1
	int endTopIdx;//stack top index after converting to SSA : mu_S_endTop#endTopIdx

	set<string> phi;//global names which need to insert phi function
	map<string, int> phiLeft;// x = phi(x, x, x ...) store : left variable name => its index

	// x = phi(x, x, x ...) store : right variable name => pair(predecessor NodeID, predecessor index)
	map<string, map<int, int>> phiRight;
	vector<Expr> phiAssign;//block end's phi assignment
	//eg : Following is a part of CFG
	//   B1  B2
	//    \    /
	//      B3
	//	B1 : x1 = ..., y3 = ...
	// B2 : x2 = ..., y1 = ...
	// B3 : x3 = phi(x1, x2)  y2 = phi(y3, y1)
	// For CFGNode B3, phiLeft is { (x, 3), (y, 2)}
	// phiRight is { (x, { (B1, 1), (B2, 2) }), (y, { (B1, 3), (B2, y1) }) }
public:
	vector<z3::expr> stack;
	map<string, z3::expr> memory;
	map<string, z3::expr> storage;

	ECFGNode(const EBasicBlock* node, const vector<int>& jumpIn, int jumpAddr, int fallsAddr, int parentID) :ID(count), node(node), jumpAddr(jumpAddr), fallsAddr(fallsAddr), jumpID(-1), fallsID(-1),
		endTop(-1), endTopIdx(-1) {
		jumpInfo = jumpIn;
		parents.insert(parentID);
		count++;
	}

	//no parent added
	ECFGNode(const EBasicBlock* node, const vector<int>& jumpIn, int jumpAddr, int fallsAddr) : ID(count), node(node), jumpAddr(jumpAddr), fallsAddr(fallsAddr), jumpID(-1), fallsID(-1),
		endTop(-1), endTopIdx(-1) {
		jumpInfo = jumpIn;
		count++;
	}

	//no specific jumpInfo added
	ECFGNode(EBasicBlock* node, int jumpAddr, int fallsAddr, int parentID) : ID(count), node(node), jumpAddr(jumpAddr), fallsAddr(fallsAddr), jumpID(-1), fallsID(-1),
		endTop(-1), endTopIdx(-1) {
		parents.insert(parentID);
		count++;
	}

	//copy constructor
	ECFGNode(const ECFGNode& c) : ID(c.ID), node(c.node), parents(c.parents), jumpInfo(c.jumpInfo), jumpAddr(c.jumpAddr), fallsAddr(c.fallsAddr), jumpID(c.jumpID), fallsID(c.fallsID), endTop(c.endTop), endTopIdx(c.endTopIdx) {
	}

	static int getCount() { return count; }

	void addParent(int parentID) {
		parents.insert(parentID);
	}
	void setID(int ID) { this->ID = ID; }
	int getID() const { return ID; }

	void setJumpID(int jumpID) { this->jumpID = jumpID; }
	int getJumpID() const { return jumpID; }

	void setFallsID(int fallsID) { this->fallsID = fallsID; }
	int getFallsID() const { return fallsID; }

	int getJumpAddr() const { return jumpAddr; }
	int getFallsAddr() const { return fallsAddr; }

	const EBasicBlock* getBlockPtr() const { return node; }

	//void setJumpIn(string jumpIn) { this->jumpIn = jumpIn; }
	static void resetCount() { count = 0; }
	string getJumpIn() const {
		string jumpIn;
		for (auto i : jumpInfo)
			jumpIn += to_string(i) + "-";
		return jumpIn.substr(0, jumpIn.length() - 1);
	}

	const vector<int>& getJumpInfo() const { return jumpInfo; }
	void setJumpInfo(const vector<int>& jumpInfo) { this->jumpInfo = jumpInfo; }
	int getStart() const { return node->getStart(); }
	int getEnd() const { return node->getEnd(); }
	BlockType getBlockType() const {
		return node->getJumpType();
	}
	const set<int>& getParents() const { return parents; }
	string genParentsStr() {
		string res = "";
		for (auto i : parents)
			res += to_string(i) + "^";
		return res;
	}

	void addExpr(int addr, Expr expr) {
		exprs[addr].push_back(expr);
		//exprs.insert(pair<int, vector<Expr>>(addr, { expr }));
	}

	void printExprs(int addr) {
		for (auto& expr : exprs[addr]) {
			expr.print();
		}
	}
	void setEndTop(int endTop) {
		this->endTop = endTop;
	}
	int getEndTop() {
		return endTop;
	}
	void setEndTopIdx(int endTopIdx) {
		this->endTopIdx = endTopIdx;
	}
	int getEndTopIdx() {
		return endTopIdx;
	}
	string getEndTopStr() {
		int condLoc = endTop + 1;
		return "mu_S_" + to_string(condLoc);
	}
	//void addTransition(Expr expr) {
	//	transitions.push_back(expr);
	//}

	void printJumpTransitions() {
		int condLoc = endTop + 1;
		cout << "mu_S_" << condLoc << " != 0" << endl;
		//for (auto& expr : transitions)
		//	expr.print();
	}
	void printNaturalTransitions() {
		int condLoc = endTop + 1;
		cout << "mu_S_" << condLoc << " == 0" << endl;
		//cout << "NOT ";
		//for (auto& expr : transitions)
		//	expr.print();
	}

	const map<int, string>& getInstrs() const {
		return node->getInstrs();
	}
	const map<int, vector<Expr>>& getExprs() const {
		return exprs;
	}
	map<int, vector<Expr>>& getExprs() {
		return exprs;
	}
	bool isMeetingPoint() const {// whether the Node is a meeting node
		return parents.size() > 1 ? true : false;
	}
	int getPhiLeftIdx(string varName) {
		assert(phiLeft.find(varName) != phiLeft.end());
		return phiLeft[varName];
	}
	const map<int, int>& getPhiRightIdx(string varName) {
		assert(phiRight.find(varName) != phiRight.end());
		return phiRight[varName];
	}

	void insertPhiAssign(unsigned int bits, string varName, int leftIdx, int rightIdx) {
		phiAssign.push_back(Expr(bits, varName, leftIdx, rightIdx));
	}
	bool hasPhiFunc(string name) {
		return phi.find(name) != phi.end();
	}
	void insertPhiFunc(string name) {//set insertion will not add repeating elements
		phi.insert(name);
	}
	void setPhiLeftIdx(string var, int index) {
		phiLeft[var] = index;
	}
	void setPhiRightIdx(string var, int NodeID, int idx) {
		phiRight[var][NodeID] = idx;
	}
	const set<string>& getPhiFuncs() const {
		return phi;
	}
	vector<Expr>& getPhiAssign() {
		return phiAssign;
	}

	const set<int>& getParents() {
		return parents;
	}

	int getLoadIndex(int pc) const {
		assert(node->getInstrs().at(pc) == "SLOAD");
		assert(exprs.at(pc).size() == 1);
		const vector<Operand>& rightOperands = (*exprs.at(pc).begin()).getRightOperand();
		assert(rightOperands.size() == 1);
		return rightOperands[0].getIndex();
	}
};