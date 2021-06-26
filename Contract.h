#pragma once
#include <string>
#include <map>
#include <vector>
#include <set>
#include <deque>
#include "rapidjson/document.h"
#include <boost/algorithm/algorithm.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include <assert.h>
#include "spdlog/spdlog.h"
#include "spdlog/sinks/stdout_color_sinks.h"
#include "spdlog/fmt/ostr.h"
#include "global.h"
#include "BasicBlock.h"
#include "Opcode.h"
#include "StackFrame.h"
#include "CFG.h"
using namespace std;
using boost::multiprecision::uint256_t;
using boost::multiprecision::int256_t;
using z3::expr;
using z3::context;
using z3::solver;
namespace bm = boost::multiprecision;
extern std::shared_ptr<spdlog::logger> console;
void generateCFG(map<int, ECFGNode>& nodes);
void buildContractCFG(CFG* cfg, map<int, ECFGNode>& nodes);
void testCFG(CFG* cfg);
class Contract {
private:
	string address;
	string name;
	string constructor;//bin-deploy

	//without src, cleanRuntime,仅表示合约代码的指令部分
	//with src, 除去constructor的部分
	string runtime;

	//without src, 不再表示swarmHash，表示的是在deploy code和runtime code之后多余的部分
	//with src, 空
	string swarmHash;

	string version;//solc version

	//optional
	const string* fileContent;
	map<int, tuple<string, string>>* srcCnts;//source file contents(fileNo => (filePath, fileContent))
	string srcmap;
	string srcmapRuntime;
	map<string, string>hashes;

	map<int, string> deployInstrs;//deploy instructions
	map<int, string> instructions;//runtime instructions

	map<int, EBasicBlock> deployBlocks;
	map<int, EBasicBlock> blocks;
	map<int, vector<string>> blockChanges;//记录 模拟执行每个block后的栈内容改变了多少
	map<int, int> blockChangedDepth;//执行每个block后栈深度的变化（负值表示栈元素变少，正值表示栈元素变多）
	map<int, int> blockMinDepth;//执行每个block时所需的栈的最小深度
	map<int, string> blockNext;//执行每个block后的跳转地址（1.确定值	2.stack[idx]）
	map<int, string> pushTagIdx;//执行每个block后的push tag所在的栈上位置
	map<int, vector<string>> tagChanges;//用以生成push tags
	//map<int, int> blockNodeNums;//每个block生成的Node数量
	map<int, set<int>> blockNodeIDs;//每个block生成的所有ID构成的集合

	map<vector<int>, int> deployJumpInfoIDMaps;
	map<vector<int>, int> jumpInfoIDMaps;//[jumpIn0, jumpIn1,...,addr] => CFGNode ID

	map<int, ECFGNode> deployNodes;//CFGNode ID => CFGNode(deploy)
	map<int, ECFGNode> runtimeNodes;//CFGNode ID => CFGNode(runtime)

	map<int, vector<string>> instrSrcmap;
	map<int, vector<string>> instrSrcmapRuntime;





	void genBasicBlocks(const map<int, string>& instructions, map<int, EBasicBlock>& blocks);

	void generateTagInstrsFile(string fileName, const set<int>& pushTags);
public:
	void genInstrSrcmap(const string& stringMap, map<int, string>& instrs, map<int, vector<string>>& instrMaps);
	void setAddress(string address) { this->address = address; }
	string getAddress() { return address; }

	void genPushTags(const map<int, ECFGNode>& nodes, int ID, vector<string>& stack, const int& addrSize, const set<int>& JUMPDESTs, set<int>& pushTags, map<int, int>& push2JumpMap, set<vector<string>>& IDVisited);
	void genFuncInTgt(const map<int, ECFGNode>& nodes, const map<int, EBasicBlock>& blocks, set<int>& potentialTgt);
	void genFuncbodyBlocks(const map<int, ECFGNode>& nodes, int funcStart, int funcStartID, map<int, map<int, tuple<int, int>>>& IDAddrs, map<int, map<int, int>>& funcEnds, map<int, map<int, vector<int>>>& FuncTopLevelIDs, set<int>& potentialTgt, int depth, map<int, vector<int>>& left, map<int, vector<int>>& funcIDs);
	void traverseBlocks(map<int, ECFGNode>& runtimeNodes, map<int, EBasicBlock>& blocks, int preID, int curBlock, vector<string>& stack, vector<int>& visited, const set<int>& natTgt, const set<int>& jmpiTgt);
	void genStackChanges(const EBasicBlock& bb, const int& addrSize, const set<int>& JUMPDESTs);
	size_t getConstructorSize() { return constructor.length(); }
	size_t getRawBinSize() { return constructor.length() + runtime.size(); }
	size_t getRawBinRuntimeSize() { return runtime.size(); }

	//将const用于成员函数表明该函数能够被const对象调用
	const string& getConstructor() const { return constructor; }
	string getRawBin() const { return constructor + runtime; }
	const string& getRawBinRuntime() { return runtime; }

	void setRawBinRuntime(const string& binRuntime) { runtime = binRuntime; }

	static void genInstrs(const string& bytecodes, map<int, string>& instrs);

	static bool isHex(string s) {
		for (size_t i = 0; i < s.size(); i++)
			if (!((s[i] >= '0' && s[i] <= '9') || (s[i] >= 'a' && s[i] <= 'f') || (s[i] >= 'A' && s[i] <= 'F')))
				return false;
		return true;

	}

	int getAddrSize();
	void genJUMPDESTs(set<int>& JUMPDESTs);
	vector<string> instrSim(int pc, string instr, vector<string>& stack, vector<string>& tagStack, const int& addrSize, const set<int>& JUMPDESTs, int& curDepth, int& minDepth);
	int instrSimulate(int pc, string instr, vector<int>& stack, const int& addrSize, const set<int>& JUMPDESTs, function<void(int, int, string, int, vector<int>&, const set<int>&)> pushOp);

	void blockTraversal(map<int, ECFGNode>& nodes, int pre, int currentBlock, vector<int>& stack, const map<int, EBasicBlock>& blocks, set<int>& blockVisited,
		map<int, set<int>>& outEdges, map<int, set<int>>& inEdges,
		const set<int>& natTgt, const set<int>& jmpiTgt, vector<int>& jumps,
		int& addrSize, const set<int>& JUMPDESTs, int pntID);

	void assertAnalysis();
	static int getOpcodeSize(string opcode);
	string getName() { return name; }

	string getSrcMap(vector<string> info) {
		int start = stoi(info[0]);
		int len = stoi(info[1]);
		int src = stoi(info[2]);
		if (src == -1)
			return "compiler-generated inline assembly statements.";
		else
			return get<1>(srcCnts->at(src)).substr(start, len);
		//return fileContent->substr(start, len);
	}
	bool hasLoop;
	bool isRecursive;

	Contract(string name, string constructor, string runtime, string swarmHash,
		string srcmap, string srcmapRuntime,
		const string* fileContent, string version)
		:name(name), constructor(constructor), runtime(runtime), swarmHash(swarmHash), srcmap(srcmap), srcmapRuntime(srcmapRuntime), fileContent(fileContent), srcCnts(NULL), version(version), hasLoop(false), isRecursive(false) {}

	void setSrcContens(map<int, tuple<string, string>>* srcCnts) {
		this->srcCnts = srcCnts;
	}

	Contract(const Contract& c)
		:name(c.name), constructor(c.constructor), runtime(c.runtime), swarmHash(c.swarmHash), srcmap(c.srcmap), srcmapRuntime(c.srcmapRuntime), fileContent(c.fileContent), srcCnts(c.srcCnts), hashes(c.hashes), version(c.version), hasLoop(c.hasLoop), isRecursive(c.isRecursive) {}

	void sloadAnalysis(set<int> allReInvAddrs = {}, set<int> invIDs = {}, map<int, int> invRelatedInstrStart = {}, map<int, int> invTypes = {}, string newBinFileName = "newsloadBin");
	void buildVerFront();
	CFG* buildCFG();

	//bool isReachable(int start, int end, vector<int>& visited, const map<int, CFGNode>& nodes);
	string transVecJumpIn(const vector<int>& jumpIn) {
		string res = "";
		for (auto& i : jumpIn) {
			res += to_string(i) + "-";
		}
		res.pop_back();
		return res;
	}

	void getJumpITgt(const map<int, EBasicBlock>& blocks, set<int>& jmpTgt);
	void getNaturalTgt(const map<int, EBasicBlock>& blocks, set<int>& natTgt);

	void genBytecodeCFG(map<int, ECFGNode>& runtimeNodes, map<int, EBasicBlock>& blocks, map<int, string>& instrs);

	void genRuntimeByteCFG();

	void setSrcmap(string srcmap) { this->srcmap = srcmap; }
	void setSrcmapRuntime(string srcmapRuntime) { this->srcmapRuntime = srcmapRuntime; }

	void genPushTags(int ID, vector<int>& stack, const int& addrSize, const set<int>& JUMPDESTs, set<int>& pushTags, map<int, int>& push2JumpMap, set<int>& blocks);

	//instr addr : decimal, pushValue hex(start with 0x)
	static void generateDisasm(const map<int, string>& instrs, string fileName);
	void generateDotGraph(const map<int, ECFGNode>& nodes, string fileName, const map<int, vector<string>>& instrSrcmapRuntime);
	void genCFGEdges(map<int, ECFGNode>& nodes);
	void genSrcMapFile(const map<int, vector<string>>& instrMaps, map<int, string>& instrs, string fileName);

	//CALLDATA/CODE/EXTCODE COPY
	//need to record memory/storage read/write(especially write)
	//stack中能计算的尽量进行计算，因为SIGNEXTEND, BYTE, SHA3(SHA3可以不用计算，但需要确定Keccak-256(x)中参数x的具体值)
	void symExecInstr(int NodeID, int pc, string instr, vector<StackFrame>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, map<int, ECFGNode>& nodes);
	void symExecNodes(map<int, ECFGNode>& runtimeNodes, const map<int, EBasicBlock>& blocks);

	void reWriteExpr(map<int, ECFGNode>& nodes);

	int NewName(const string& varName, map<string, int>& counter, map<string, vector<int>>& stack);
	void rename(int NodeID, const map<int, set<int>>& graph, map<int, ECFGNode>& nodes, map<string, int>& counter, map<string, vector<int>>& stack, const map<int, int>& IDom, const map<int, set<int>>& dTree);

	void genSSAFile(map<int, ECFGNode>& nodes, string fileName);

	//仅做测试使用 不属于类成员
	void redundantSLOADOptimize(set<int> allReInvAddrs = {}, set<int> invIDs = {}, map<int, int> invRelatedInstrStart = {}, map<int, int> invTypes = {}, string newBinFileName = "newsloadBin");
	void testSymStack(map<int, ECFGNode>& runtimeNodes);

	void assertAndSloadAnalysis();
};

map<int, vector<z3::expr>> getCODECOPYOffsetAndSizeExpr(const map<int, EBasicBlock>& blocks, const map<int, int>& codecopyBlocks, z3::context& ctx);
void symExecInstr(int pc, string instr, z3::context& c, vector<z3::expr>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, z3::expr& jumpiCond);
void stackOp1(vector<string>& stack);
void stackOp2(vector<string>& stack);
void processReturnData(const z3::expr& out, const z3::expr& outSize, map<string, z3::expr>& memory);
extern z3::expr* returnDataSize;
bool reachable(const map<int, ECFGNode>& nodes, int start, int end);
void postDFS(int ID, const map<int, set<int>>& reEdges, set<int>& visited, vector<int>& stack);
map<int, int> genIDom(const map<int, set<int>>& graph);
class InstrState {
public:
	vector<z3::expr> stack;
	map<string, z3::expr> memory;
	map<string, z3::expr> storage;
};

void displayStackFrame(const vector<StackFrame>& stack);
//void processSymExpr(string& symExpr, bool symbolic = true);

class CFGLoc {
public:
	int NodeID;
	int pc;
	CFGLoc(int NodeID, int pc) : NodeID(NodeID), pc(pc) {}
	CFGLoc() : NodeID(-1), pc(-1) {}
	bool operator<(const CFGLoc& c) const {
		if (NodeID != c.NodeID)
			return NodeID < c.NodeID;
		else
			return pc < c.pc;
	}

	bool operator==(const CFGLoc& c) const {
		return NodeID == c.NodeID && pc == c.pc;
	}

	bool operator!=(const CFGLoc& c) const {
		return !((*this) == c);
	}
	string to_string() const {
		return "NodeID_" + std::to_string(NodeID) + "-" + "pc_" + std::to_string(pc);
	}
};

class PartBasicBlock {
public:
	int blockStart;
	int start;
	int end;

	PartBasicBlock(int blockStart, int start, int end) : blockStart(blockStart), start(start), end(end) {}
	bool operator< (const PartBasicBlock& p) const {
		if (start != p.start)
			return start < p.start;
		else
			return end < p.end;
	}
	bool operator== (const PartBasicBlock& p) const {
		return start == p.start && end == p.end;
	}
};

class PartBasicBlockWithInstrUpdates {
public:
	int blockStart;
	int start;
	int end;

	set<int> deInstrs;
	map<int, string> updateInstrs;

	PartBasicBlockWithInstrUpdates(int blockStart, int start, int end) : blockStart(blockStart), start(start), end(end) {}
	bool operator< (const PartBasicBlockWithInstrUpdates& p) const {
		if (start != p.start)
			return start < p.start;
		else if (end != p.end)
			return end < p.end;
		else if (deInstrs != p.deInstrs)
			return deInstrs < p.deInstrs;
		else
			return updateInstrs < p.updateInstrs;
	}
	bool operator== (const PartBasicBlockWithInstrUpdates& p) const {
		return start == p.start && end == p.end && deInstrs == p.deInstrs && updateInstrs == p.updateInstrs;
	}
};

class ReSloadChain {
public:
	ReSloadChain() {}
	CFGLoc start;
	set<CFGLoc> end;
	map<int, PartBasicBlock> pbbs;
	map<int, set<int>> partEdges;
};

//该类中所涉及到的基本块内指令的修改一定不会涉及到push tag
class BlockInstrsChanges {
public:
	BlockInstrsChanges() {}
	int blockStart;
	set<int> deInstrs;//删
	map<int, string> updateInstrs;//增，改

	bool operator==(const BlockInstrsChanges& bic) const {
		return blockStart == bic.blockStart && deInstrs == bic.deInstrs && updateInstrs == bic.updateInstrs;
	}
};

void getDstIDPaths(const map<int, set<int>>& edges, const set<int>& dstIDs, map<int, vector<int>>& paths);
void genCallChain(int ID, const vector<int>& path, const map<int, ECFGNode>& nodes, const map<int, map<int, tuple<int, int>>>& IDAddrs, const map<int, map<int, int>>& funcEnds, vector<int>& callAddrChain, vector<int>& callIDChain);