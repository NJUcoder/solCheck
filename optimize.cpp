#include "Contract.h"
#include <queue>
#include<unordered_set>
using namespace std;

void genTagInstrs(const map<int, string>& instructions, set<int>& pushTags, const set<int>& JUMPDESTs, map<int, string>& tagInstrs) {
	map<int, int> tags;//JUMPDEST地址 => tag值
	int tagCnt = 0;
	for (auto& i : JUMPDESTs) {
		tags.insert(make_pair(i, tagCnt));
		tagCnt++;
	}
	for (auto& instr : instructions)
		if (pushTags.find(instr.first) != pushTags.end()) {
			vector<string> temp;
			boost::split(temp, instr.second, boost::is_any_of(" "));
			int addr = -1;
			SSCANF(temp[1].c_str(), "%x", &addr);
			int tagName = tags.at(addr);
			tagInstrs.insert(make_pair(instr.first, temp[0] + " tag" + to_string(tagName)));
		}
		else if (instr.second == "JUMPDEST")
			tagInstrs.insert(make_pair(instr.first, "tag" + to_string(tags.at(instr.first))));
		else
			tagInstrs.insert(make_pair(instr.first, instr.second));
}

pair<int, int> getSrcFunc(int addr, const map<int, int>& functions) {
	for (auto& f : functions)
		if (addr > f.first && addr < f.second)
			return f;

	assert(false);
	return pair<int, int>();
}

void genEnd2Start(const map<int, ECFGNode>& runtimeNodes, map<int, int>& res) {
	for (auto& n : runtimeNodes)
		if (res.find(n.second.getEnd()) == res.end())
			res.insert(make_pair(n.second.getEnd(), n.second.getStart()));
}

int genNewTagCnt() {
	static int tagCnt = -1;
	tagCnt++;
	return tagCnt;
}

void generateEnd2Start(const map<int, string>& instrs, map<int, int>& end2Start) {
	int i = 0;
	int pre = -1;
	for (auto& instr : instrs) {
		if (instr.second == "JUMPI" || instr.second == "JUMP" || instr.second == "CREATE" || instr.second == "CALL" || instr.second == "CALLCODE" || instr.second == "DELEGATECALL" ||
			instr.second == "STATICCALL" || instr.second == "INVALID" || instr.second == "SELFDESTRUCT" || instr.second == "STOP" || instr.second == "RETURN") {
			end2Start.insert(make_pair(instr.first, i));
			i = instr.first + 1;
		}
		else if (instr.second == "JUMPDEST") {
			end2Start.insert(make_pair(pre, i));
			i = instr.first;
		}
		pre = instr.first;
	}
}
int getInstrFuncStart(int instr, const map<int, int>& start2End) {
	for (auto& i : start2End)
		if (instr >= i.first && instr <= i.second)
			return i.first;
	assert(false);
	return -1;
}
string genCallChainString(const vector<int>& vec) {
	assert(!vec.empty());
	string res = to_string(vec[0]);
	for (size_t i = 1; i < vec.size(); i++)
		res += "_" + to_string(vec[i]);
	return res;
}
void genCallChainDotFile(const map<vector<int>, set<vector<int>>>& callChainGraph, const map<vector<int>, int>& addrCallChain2ID, const map<int, ECFGNode>& runtimeNodes, const string& fileName) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& i : callChainGraph) {
		string type;
		if (i.second.empty()) {
			int id = addrCallChain2ID.at(i.first);
			if (runtimeNodes.at(id).getBlockType() == BlockType::INVALID)
				type = "(INVALID)";
			else
				type = "(SLOAD)";
		}

		string str = genCallChainString(i.first);
		string nodeName = "Node_" + str;
		string label = str + type;
		dotFile += nodeName + "[label = \"" + label + "\"]\r\n";
		for (auto& chd : i.second) {
			string chdName = "Node_" + genCallChainString(chd);
			dotFile += "\t" + nodeName + " -> " + chdName + ";\r\n";
		}
	}

	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}
class FuncBody {
public:
	int funcStart;
	set<int> delInvs;//这里隐含了一个假设：在一函数体内部，同一INVALID地址不可能生成两个CFGNode
	map<int, BlockInstrsChanges*> sloadRelChanges;//key值为sload相关基本块,value为指令优化做出的改变，这里也隐含假设：在同一函数体内部，同一SLOAD基本块不可能生成两个CFGNode
	//注意以上同一基本块不可能生成两个CFGNode，指的是这些CFGNode的最内层调用不可能一样
	map<int, FuncBody*> jumpIns;//需要修改的jumpIn
	FuncBody(int funcStart) :funcStart(funcStart)/*, num(0)*/ {}
	//int num;

	bool operator==(const FuncBody& right) const {
		if (funcStart == right.funcStart && delInvs == right.delInvs) {
			if (sloadRelChanges.size() != right.sloadRelChanges.size())
				return false;
			for (auto& i : sloadRelChanges)
				if (right.sloadRelChanges.find(i.first) == right.sloadRelChanges.end() || !(*(right.sloadRelChanges.at(i.first)) == *i.second))
					return false;
			if (jumpIns.size() != right.jumpIns.size())
				return false;
			for (auto& i : jumpIns)
				if (right.jumpIns.find(i.first) == right.jumpIns.end() || !(*(right.jumpIns.at(i.first)) == *(i.second)))
					return false;

			return true;
		}
		return false;
	}


};
class FuncBodyHash {
public:
	size_t operator()(const FuncBody& fb) const {
		size_t h = hash<int>()(fb.funcStart);
		for (auto& i : fb.delInvs)
			h ^= hash<string>()("^" + to_string(i));
		for (auto& i : fb.jumpIns)
			h ^= hash<string>()("$" + to_string(i.first));
		for (auto& i : fb.sloadRelChanges) {
			h ^= hash<string>()("%" + to_string(i.first));
			//h ^= hash<string>()("&" + to_string(i.second));
		}
		return h;
	}
};

//生成函数体起始地址 =》 所有跳转到该起始地址的jump In addr
//注意是 jump In Addr 不是jump In所在基本块的起始地址
void genFuncStartJumpInMapping(const map<int, ECFGNode>& runtimeNodes, const map<int, int>& functions, map<int, set<int>>& mapping) {
	map<int, int> end2Start;
	for (auto& f : functions)
		end2Start.insert(make_pair(f.second, f.first));

	queue<int> que;
	que.push(0);
	set<int> visited;
	while (!que.empty()) {
		const ECFGNode& front = runtimeNodes.at(que.front());
		int frontStart = front.getStart();
		set<int> chdIDs;
		if (front.getJumpID() != -1)
			chdIDs.insert(front.getJumpID());
		if (front.getFallsID() != -1)
			chdIDs.insert(front.getFallsID());
		for (auto& c : chdIDs)
			if (visited.find(c) == visited.end()) {
				visited.insert(c);
				que.push(c);
				int cStart = runtimeNodes.at(c).getStart();
				if (functions.find(cStart) != functions.end())
					mapping[cStart].insert(front.getEnd());
			}

		que.pop();
	}
}

void genFuncBodyInstrs(const FuncBody& fb, const map<int, string>& reInstrs, const map<int, EBasicBlock>& blocks, const map<int, map<int, tuple<int, int>>>& IDAddrs, const map<int, int>& push2JumpMap, int& instrStart, const map<int, int>& invRelatedInstrStart, const map<int, int>& invTypes, const unordered_map<FuncBody, int, FuncBodyHash>& optimizedFuncBodys, map<int, string>& resInstrs, const map<int, int>& originalTags, map<int, map<int, int>>& funcBlockNums, const map<int, int>& codecopyAddr2offsetAddr, map<int, int>& newOffsetAddr2OldCodeCopyInstrs) {
	map<int, int> offsetAddr2codecopyAddr;
	for (auto& i : codecopyAddr2offsetAddr) {
		//offset和codecopy应该是一一对应的
		assert(offsetAddr2codecopyAddr.find(i.second) == offsetAddr2codecopyAddr.end());
		offsetAddr2codecopyAddr.insert(make_pair(i.second, i.first));
	}

	if (funcBlockNums.find(fb.funcStart) == funcBlockNums.end()) {
		map<int, int> blockNums;//存储一个函数体所包含的所有基本块以及在函数体中基本块出现的个数

		for (auto& id : IDAddrs.at(fb.funcStart))
			if (get<1>(id.second) == 0)
				blockNums[get<0>(id.second)]++;

		assert(blockNums.at(fb.funcStart) == 1);
		funcBlockNums.insert(make_pair(fb.funcStart, blockNums));
	}

	const map<int, int>& blockNums = funcBlockNums.at(fb.funcStart);
	//函数体首地址一定为JUMPDEST，其tag需要另行确定
	map<int, int> JUMPDESTtags;

	//即使某一基本块在函数体内部出现多次，该基本块也只需要生成一次
	//1.与地址无关的指令当然只需要生成一次
	//push addr的指令
		//addr是函数体内部指令，也只需要复制一次
		//addr是外部函数，同上
		//addr是优化后的函数，应该不会出现不同的节点分别调用优化后的函数和优化前的函数，当然从取巧的角度而言，这个不重要，因为不论跳入的函数体有没有优化，只需要保证跳入的是同一函数就行
	//JUMPDEST指令，只需要一次
	for (auto& bb : blockNums)
		for (int i = 0; i < bb.second; i++) {
			int blockStart = bb.first;
			int blockEnd = blocks.at(bb.first).getEnd();
			const map<int, string>& tempInstrs = blocks.at(bb.first).getInstrs();
			//auto iter = reInstrs.find(blockStart);
			//auto end = reInstrs.find(blockEnd); end++;
			for (auto& t : tempInstrs) {
				auto iter = reInstrs.find(t.first);
				if (iter != reInstrs.end())
					if (iter->second == "JUMPDEST")
						JUMPDESTtags.insert(make_pair(iter->first, genNewTagCnt()));
			}
		}

	//冗余相关的基本块在函数体内部应该只有一个(未经过实验验证)
	//冗余相关的基本块应该是地址上连续的基本块(未经过实验验证)

	//这里默认冗余相关的基本块应该是连续的且在函数体内部只有一个实例
	//这里不存在冗余相关指令被提前删除的情况
	unordered_set<int> delInstrs;

	//changeInstrs存储了需要改动的指令地址和改动后的指令
	map<int, string> changeInstrs;
	for (auto& inv : fb.delInvs) {
		int start = invRelatedInstrStart.at(inv);
		if (invTypes.at(inv) == 1) {
			int end = inv + 1;
			for (auto iter = reInstrs.find(start); iter != reInstrs.find(end); iter++)
				delInstrs.insert(iter->first);
			delInstrs.insert(end);
		}
		else if (invTypes.at(inv) == 2) {
			auto invIter = reInstrs.find(inv);
			invIter--;
			changeInstrs.insert(make_pair(invIter->first, "JUMP"));
			invIter--;
			for (auto iter = reInstrs.find(start); iter != invIter; iter++)
				delInstrs.insert(iter->first);
			delInstrs.insert(inv);
		}
	}

	//这里也假设冗余SLOAD相关的基本块在函数体内部应该有且只有一个
	for (auto& bic : fb.sloadRelChanges) {
		for (auto& d : bic.second->deInstrs)
			delInstrs.insert(d);
		for (auto& c : bic.second->updateInstrs)
			changeInstrs.insert(c);
	}

	bool debug = false;
	if (debug)
		displayGreenMsg("FuncStart : " + to_string(fb.funcStart));

	for (auto& bb : blockNums) {
		int blockStart = bb.first;
		int blockEnd = blocks.at(bb.first).getEnd();
		const map<int, string>& tempInstrs = blocks.at(bb.first).getInstrs();
		for (auto& t : tempInstrs) {
			auto iter = reInstrs.find(t.first);
			if (iter == reInstrs.end()) {
				if (debug)
					displayRedMsg(to_string(instrStart) + " " + to_string(t.first) + " " + t.second + "\t" + "previous deleted");
				continue;
			}
			else if (iter->first == fb.funcStart) {
				assert(bb.second == 1);
				int tagNum = optimizedFuncBodys.at(fb);
				resInstrs.insert(make_pair(instrStart, "tag " + to_string(tagNum)));
				if (debug)
					displayBlueMsg(to_string(instrStart) + " " + to_string(iter->first) + " " + iter->second + "\t" + resInstrs.at(instrStart));
				instrStart++;
			}
			else if (changeInstrs.find(iter->first) != changeInstrs.end()) {
				resInstrs.insert(make_pair(instrStart, changeInstrs.at(iter->first)));
				if (debug)
					displayYellowMsg(to_string(instrStart) + " " + to_string(iter->first) + " " + iter->second + "\t" + resInstrs.at(instrStart));
				instrStart++;
			}
			else if (delInstrs.find(iter->first) == delInstrs.end()) {
				if (iter->second == "JUMPDEST") {
					resInstrs.insert(make_pair(instrStart, "tag " + to_string(JUMPDESTtags.at(iter->first))));
					if (debug)
						displayCyanMsg(to_string(instrStart) + " " + to_string(iter->first) + " " + iter->second + "\t" + resInstrs.at(instrStart));
				}
				else if (push2JumpMap.find(iter->first) != push2JumpMap.end()) {
					int jumpAddr = push2JumpMap.at(iter->first);

					vector<string> temp;
					boost::split(temp, iter->second, boost::is_any_of(" "));
					int pushValue;
					SSCANF(temp[1].c_str(), "%x", &pushValue);
					int tagNum = -1;
					//PUSH Addr分为两种情况
					//1.函数体内部跳转
					//2.跳转到另一函数体
					//2.1 跳转的函数体不需要改动
					//2.2 跳转的函数体由于消除冗余的关系 需要进行修改
					if (JUMPDESTtags.find(pushValue) != JUMPDESTtags.end())
						tagNum = JUMPDESTtags.at(pushValue);
					else if (fb.jumpIns.find(jumpAddr) == fb.jumpIns.end()) {
						tagNum = originalTags.at(pushValue);
					}
					else
						tagNum = optimizedFuncBodys.at(*(fb.jumpIns.at(jumpAddr)));

					string newInstr = "push tag " + to_string(tagNum);
					resInstrs.insert(make_pair(instrStart, newInstr));

					if (debug)
						displayPurpleMsg(to_string(instrStart) + " " + to_string(iter->first) + " " + iter->second + "\t" + resInstrs.at(instrStart));
				}
				else {
					if (offsetAddr2codecopyAddr.find(iter->first) != offsetAddr2codecopyAddr.end())
						newOffsetAddr2OldCodeCopyInstrs.insert(make_pair(instrStart, offsetAddr2codecopyAddr.at(iter->first)));
					resInstrs.insert(make_pair(instrStart, iter->second));
					if (debug)
						cout << to_string(instrStart) << " " << iter->first << " " << iter->second << "\t" << resInstrs.at(instrStart) << endl;
				}
				instrStart++;
			}
			else
				if (debug)
					displayRedMsg(to_string(instrStart) + " " + to_string(iter->first) + " " + iter->second + "\t" + "deleted");
		}
	}
}

void displayIntVector(const vector<int>& vec) {
	for (auto& i : vec)
		cout << i << " ";
	cout << endl;
}

void generateOriginalTagInstrs(string fileName, const map<int, string>& instrs, const map<int, int>& originalTags, const map<int, int>& push2JumpMap) {
	ofstream outFile(fileName);
	for (auto& i : instrs) {
		if (i.second == "JUMPDEST") {
			outFile << i.first << " : tag " << originalTags.at(i.first) << endl;
		}
		else if (push2JumpMap.find(i.first) != push2JumpMap.end()) {
			vector<string> temp;
			boost::split(temp, i.second, boost::is_any_of(" "));
			int pushValue = -1;
			SSCANF(temp[1].c_str(), "%x", &pushValue);
			outFile << i.first << " : push tag " << originalTags.at(pushValue) << endl;
		}
		else
			outFile << i.first << " : " << i.second << endl;
	}
	outFile.close();
}

void generateFunc2JumpInIDMap(const map<int, ECFGNode>& runtimeNode, const map<int, map<int, tuple<int, int>>>& IDAddrs, map<int, set<int>>& funcStart2JumpInID) {
	queue<int> que;
	que.push(0);
	set<int> IDVisited;
	while (!que.empty()) {
		int front = que.front();
		const ECFGNode& node = runtimeNode.at(front);
		int jumpAddr = node.getJumpAddr();
		int jumpID = node.getJumpID();
		int fallsID = node.getFallsID();
		if (jumpID != -1 && IDVisited.find(jumpID) == IDVisited.end()) {
			que.push(jumpID);
			IDVisited.insert(jumpID);
		}
		if (fallsID != -1 && IDVisited.find(fallsID) == IDVisited.end()) {
			que.push(fallsID);
			IDVisited.insert(fallsID);
		}

		if (jumpAddr != -1 && IDAddrs.find(jumpAddr) != IDAddrs.end())
			funcStart2JumpInID[jumpAddr].insert(node.getID());

		que.pop();
	}
}

bool contains(const set<int>& pnt, const set<int>& chd) {
	for (auto& i : chd)
		if (pnt.find(i) == pnt.end())
			return false;
	return true;
}

void genInvRelatedJumpIns(const map<int, ECFGNode>& runtimeNodes, const map<int, int>& blockEnd2Start, const map<int, set<vector<int>>>& IDCallIDChain, const map<int, vector<int>>& paths, map<int, set<int>>& funcStart2JumpInID) {
	for (auto& chains : IDCallIDChain)
		for (auto& chain : chains.second)
			for (auto iter = chain.rbegin() + 1; iter != chain.rend(); iter++) {
				int jumpInID = *iter;
				int funcStartID = runtimeNodes.at(jumpInID).getJumpID();
				int funcStart = runtimeNodes.at(jumpInID).getJumpAddr();

				//由于solc 优化的原因，所以一个函数起始块的Node可能由不同的地址跳入
				for (auto& pnt : runtimeNodes.at(funcStartID).getParents())
					if (pnt != -1)
						funcStart2JumpInID[funcStart].insert(pnt);
			}
}

void genCallChain(int ID, const vector<int>& path, const map<int, ECFGNode>& nodes, const map<int, map<int, tuple<int, int>>>& IDAddrs, const map<int, map<int, int>>& funcEnds, vector<int>& callAddrChain, vector<int>& callIDChain) {
	int controlID = path[0];//遍历路径时的对照Node ID
	vector<int> depths;
	bool inFunc = false;
	int curFunc = -1;
	//cout << setw(12) << "Idx" << setw(12) << "NodeID" << setw(12) << "ControlID" << setw(12) << "BlockStart" << setw(12) << "FuncDepth" << endl;
	for (size_t i = 0; i < path.size(); i++) {
		int bb = nodes.at(path[i]).getStart();
		if (!inFunc && IDAddrs.find(bb) != IDAddrs.end()) {
			//IDAddrs能很好地规避同一函数体中出现多次相同的基本块的情况
			curFunc = bb;
			int tempID = -1;
			for (auto& id : IDAddrs.at(bb)) {
				int start = get<0>(id.second);
				if (start == bb)
					if (tempID == -1)
						tempID = id.first;
					else
						//这里有一个基本假设：函数起始块在函数体中只能出现一次
						assert(false);
			}
			controlID = tempID;
			inFunc = true;
		}
		else if (inFunc) {//inFunc为true时i一定大于0，因为起始节点不可能为函数体起始块
			int curID = path[i];
			int preID = path[i - 1];
			if (nodes.at(preID).getJumpID() == curID)
				controlID = nodes.at(controlID).getJumpID();
			if (nodes.at(preID).getFallsID() == curID)
				controlID = nodes.at(controlID).getFallsID();
		}
		else
			controlID = path[i];
		if (inFunc)
			depths.push_back(get<1>(IDAddrs.at(curFunc).at(controlID)) + 1);
		else
			depths.push_back(0);
		if (inFunc && funcEnds.at(curFunc).find(controlID) != funcEnds.at(curFunc).end()) {
			inFunc = false;
		}

		//cout << setw(12) << i << setw(12) << path[i] << setw(12) << controlID << setw(12) << nodes.at(path[i]).getStart() << setw(12) << depths[i] << endl;
	}

	for (int i = 1; i < depths.size(); i++) {
		if (depths[i - 1] < depths[i]) {
			assert(depths[i - 1] + 1 == depths[i]);//JUMP [in]每次只能跳入一层
			int jumpInAddr = nodes.at(path[i - 1]).getEnd();
			callAddrChain.push_back(jumpInAddr);
			callIDChain.push_back(path[i - 1]);
			int funcIn = nodes.at(path[i]).getStart();
		}
		else if (depths[i - 1] > depths[i])
			for (int j = depths[i - 1]; j > depths[i]; j--) {//JUMP [out]每次可以跳出多层
				callAddrChain.pop_back();
				callIDChain.pop_back();
			}
	}
	callAddrChain.push_back(nodes.at(ID).getStart());
	callIDChain.push_back(ID);
}

void pruningInvalids(const set<int>& partReIDs, const map<int, ECFGNode>& nodes, map<int, set<int>>& edges, const set<int>& potentialJumpInTgt, set<int>& delFunc) {
	vector<int> invalids;

	map<int, set<int>> reverseEdges;
	for (auto& n : nodes) {
		if (partReIDs.find(n.first) != partReIDs.end())
			invalids.push_back(n.first);
		for (auto& pnt : n.second.getParents())
			if (pnt != -1)
				reverseEdges[n.first].insert(pnt);
	}
	set<int> visited;
	for (auto inv : invalids) {
		list<int> que;
		que.push_back(inv);
		while (!que.empty()) {
			int i = que.front();
			visited.insert(i);
			que.pop_front();

			//Node 0 has no reverse edges
			if (reverseEdges.find(i) == reverseEdges.end())
				continue;
			for (auto j : reverseEdges.at(i)) {
				if (visited.find(j) == visited.end())
					que.push_back(j);
			}
		}
	}
}

//由于部分指令被修改为一串指令，但一串指令不会影响基本块的划分，当然会影响栈中元素的变化

string tagInstrSim(string instr, vector<string>& stack, int& curDepth, int& minDepth, const map<int, int>& tagNum2Addr) {
	string target = "1";
	vector<string> instrParts;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string& opcode = instrParts[0];
	if (opcode == "push") {
		int tagNum = stoi(instrParts[2]);
		stack.push_back("-" + to_string(tagNum2Addr.at(tagNum)));
		curDepth++;
	}
	else if (opcode.find("tag") != string::npos) {
		return target;
	}
	else if (isLowercaseHex(opcode)) {
		map<int, string> opInstrs;
		Contract::genInstrs(opcode, opInstrs);
		string tgt;
		for (auto& i : opInstrs) {
			tgt = tagInstrSim(i.second, stack, curDepth, minDepth, tagNum2Addr);
		}
		return tgt;
	}
	else {
		int bytecode = Opcode::getOpcode(opcode);
		int before = int(stack.size());
		switch (bytecode) {
		case 0x57: {//JUMPI
			target = stack.back();
			stack.pop_back(); stack.pop_back();
			curDepth -= 2;
			minDepth = minDepth > curDepth ? curDepth : minDepth;
			break;
		}
		case 0x56: {//JUMP
			target = stack.back();
			stack.pop_back();
			curDepth--;
			minDepth = minDepth > curDepth ? curDepth : minDepth;
			break;
		}
		case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
		case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
			//PUSHx
			stack.push_back("1");
			curDepth++;
			break;
		}
		case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
			//DUPx
			size_t index = atoi(opcode.substr(3).c_str());//index : 1~16
			stack.push_back(stack[stack.size() - index]);

			int depth = curDepth - int(index);
			minDepth = minDepth > depth ? depth : minDepth;
			curDepth++;

			break;
		}
		case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
			//SWAPx
			size_t index = atoi(opcode.substr(4).c_str());//index : 1~16
			int size = (int)stack.size();
			string temp = stack.back();
			stack[size - 1] = stack[size - index - 1];
			stack[size - index - 1] = temp;

			int depth = curDepth - int(index) - 1;
			minDepth = minDepth > depth ? depth : minDepth;
			break;
		}
		case 0x16:case 0x17: case 0x18:case 0x03:case 0x04:case 0x1b:case 0x1c: {
			//AND OR XOR SUB DIV SHL SHR
			stackOp1(stack);

			curDepth -= 2;//使用栈上的两个操作数
			minDepth = minDepth > curDepth ? curDepth : minDepth;
			curDepth++;
			break;
		}
		case 0x01:case 0x02: {
			//ADD MUL
			stackOp2(stack);

			curDepth -= 2;//使用栈上的两个操作数
			minDepth = minDepth > curDepth ? curDepth : minDepth;
			curDepth++;
			break;
		}
		default: {//other opcodes
			tuple<int, int> op = Opcode::getOperation(bytecode);
			int delta = get<0>(op);//pop stack
			int alpha = get<1>(op);//push stack
			for (int i = 0; i < delta; i++) {
				stack.pop_back();
			}
			for (int i = 0; i < alpha; i++) {
				stack.push_back("1");
			}

			curDepth -= delta;
			minDepth = minDepth > curDepth ? curDepth : minDepth;
			curDepth += alpha;
			break;
		}
		}
		int after = int(stack.size());
		assert(before - after == get<0>(Opcode::getOperation(bytecode)) - get<1>(Opcode::getOperation(bytecode)));
	}
	return target;
}

//blockChanges记录 模拟执行每个block后的栈内容改变了多少
//blockMinDepth执行每个block时所需的栈的最小深度
//blockNext执行每个block后的跳转地址（1.确定值	2.stack[idx]）
void genTagStackChanges(const EBasicBlock& bb, map<int, vector<string>>& blockChanges, map<int, int>& blockMinDepth, map<int, string>& blockNext, const map<int, int>& tagNum2Addr) {
	vector<string> testStack;
	//s1023,s1022,...,s1,s0
	//之所以选1024是因为solidity的默认栈最大深度为1024
	const int MAXDEPTH = 1024;
	for (int i = MAXDEPTH - 1; i >= 0; i--)
		testStack.push_back("s" + to_string(i));
	//string target = "-1";
	int curDepth = 0;
	int minDepth = 0;
	string tgt;
	for (auto& i : bb.getInstrs()) {
		tgt = tagInstrSim(i.second, testStack, curDepth, minDepth, tagNum2Addr);

		//displayGreenMsg(to_string(i.first) + " " + i.second);
		//for (int i = 1024 + minDepth; i < testStack.size(); i++)
		//	cout << testStack[i] << " ";
		//cout << " : TOP" << endl;
		//string dep = "curDepth : " + to_string(curDepth) + ", minDepth : " + to_string(minDepth);
		//displayRedMsg(dep);
	}

	blockChanges[bb.getStart()] = { };
	for (int i = MAXDEPTH + minDepth; i < testStack.size(); i++) {
		blockChanges.at(bb.getStart()).push_back(testStack[i]);
	}
	blockMinDepth.insert(make_pair(bb.getStart(), minDepth));
	blockNext.insert(make_pair(bb.getStart(), tgt));
}

//执行到该基本块的模拟栈内容 + 基本块首地址
static set<vector<string>>stackKeys;
void traverseTagBlocks(const map<int, EBasicBlock>& blocks, int curBlock, vector<string>& stack, const map<int, vector<string>>& blockChanges, const map<int, int>& blockMinDepth, const map<int, string>& blockNext, set<int>& blockVisited) {
	//displayBlueMsg("curBlock before stack : " + to_string(curBlock));
	//cout << "\t";
	//for (auto& i : stack)
	//	cout << i << " ";
	//cout << " : TOP" << endl;
	blockVisited.insert(curBlock);

	const EBasicBlock& bb = blocks.at(curBlock);
	vector<string> change = blockChanges.at(curBlock);
	int minDepth = blockMinDepth.at(curBlock);
	assert(stack.size() >= -minDepth);
	vector<string> after;
	for (size_t i = 0; i < stack.size() + minDepth; i++)
		after.push_back(stack[i]);
	for (size_t i = 0; i < change.size(); i++)
		if (change[i][0] != 's')
			after.push_back(change[i]);
		else {
			size_t lastIdx = stoi(change[i].substr(1));
			after.push_back(stack[stack.size() - 1 - lastIdx]);
		}

	string next = blockNext.at(curBlock);
	int target = -1;
	if (next[0] == 's') {
		size_t lastIdx = stoi(next.substr(1));
		SSCANF(stack[stack.size() - 1 - lastIdx].substr(1).c_str(), "%d", &target);
	}
	else
		SSCANF(next.substr(1).c_str(), "%d", &target);
	if (bb.getJumpType() == BlockType::JUMPI) {
		int jumpAddr = target;
		auto nextBlockIter = blocks.find(curBlock);
		nextBlockIter++;

		int fallsAddr = nextBlockIter->first;

		stack.push_back(to_string(curBlock));
		stackKeys.insert(stack);

		vector<string> key = after; key.push_back(to_string(jumpAddr));

		vector<string> dupStack = after;
		if (stackKeys.find(key) == stackKeys.end())
			traverseTagBlocks(blocks, jumpAddr, after, blockChanges, blockMinDepth, blockNext, blockVisited);
		key.pop_back(); key.push_back(to_string(fallsAddr));
		if (stackKeys.find(key) == stackKeys.end())
			traverseTagBlocks(blocks, fallsAddr, dupStack, blockChanges, blockMinDepth, blockNext, blockVisited);
	}
	else if (bb.getJumpType() == BlockType::JUMP) {
		int jumpAddr = target;
		stack.push_back(to_string(curBlock));
		stackKeys.insert(stack);

		vector<string> key = after; key.push_back(to_string(jumpAddr));
		if (stackKeys.find(key) == stackKeys.end())
			traverseTagBlocks(blocks, jumpAddr, after, blockChanges, blockMinDepth, blockNext, blockVisited);
	}
	else if (bb.getJumpType() == BlockType::CREATE || bb.getJumpType() == BlockType::MESSAGECALL || bb.getJumpType() == BlockType::NATURAL) {
		auto nextIter = blocks.find(curBlock);
		nextIter++;
		int fallsAddr = nextIter->first;

		stack.push_back(to_string(curBlock));
		stackKeys.insert(stack);

		vector<string> key = after; key.push_back(to_string(fallsAddr));
		if (stackKeys.find(key) == stackKeys.end())
			traverseTagBlocks(blocks, fallsAddr, after, blockChanges, blockMinDepth, blockNext, blockVisited);
	}
	else if (bb.getJumpType() == BlockType::REVERT || bb.getJumpType() == BlockType::INVALID || bb.getJumpType() == BlockType::RETURN || bb.getJumpType() == BlockType::STOP || bb.getJumpType() == BlockType::SELFDESTRUCT) {
		stack.push_back(to_string(curBlock));
		stackKeys.insert(stack);
	}
}

//void getTagJumpITgt(const map<int, EBasicBlock>& blocks,const map<int, int>& tagNum2Addr, set<int>& jmpTgt) {
//	for (auto& bb : blocks)
//		//Here assume JUMPI's jump target is pushed into the stack by the previous instruction
//		if (bb.second.getJumpType() == JUMPI) {
//			map<int, string>::const_reverse_iterator riter = bb.second.getInstrs().rbegin();
//			riter++;
//			int pushPc = riter->first;
//			string instr = riter->second;
//			//仅通过字节码序列构建时由于未去除掉末尾冗余指令(metahash相关),所以末尾冗余指令可能会出现JUMPI指令的上一条指令不为PUSH指令的现象
//			if (instr.find("push") != string::npos) {
//				vector<string> instrParts;
//				boost::split(instrParts, instr, boost::is_any_of(" "));
//				int tagNum = stoi(instrParts[1].substr(3));
//				jmpTgt.insert(tagNum2Addr.at(tagNum));
//			}
//		}
//}
//void getTagNaturalTgt(const map<int, EBasicBlock>& blocks, set<int>& natTgt) {
//	for (auto& bb : blocks)
//		if (bb.second.getJumpType() == JUMPI ||
//			bb.second.getJumpType() == CREATE || bb.second.getJumpType() == MESSAGECALL ||
//			bb.second.getJumpType() == NATURAL) {
//			int end = bb.second.getEnd();
//			int tgt = end + Contract::getOpcodeSize(bb.second.getInstrs().at(end));
//			natTgt.insert(tgt);
//		}
//}

void genBasicBlocks(const map<int, string>& instructions, map<int, EBasicBlock>& blocks) {
	map<int, BlockType> blockEndInfo;
	vector<int> ends;
	int preInstrAddr = 0;//here preAddr means block start
	for (auto instr : instructions) {
		if (instr.second == "JUMPI") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::JUMPI));
			ends.push_back(instr.first);
		}
		else if (instr.second == "JUMP") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::JUMP));
			ends.push_back(instr.first);
		}
		else if (instr.second == "CREATE") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::CREATE));
			ends.push_back(instr.first);
		}
		else if (instr.second == "CALL" || instr.second == "CALLCODE" || instr.second == "DELEGATECALL" || instr.second == "STATICCALL") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::MESSAGECALL));
			ends.push_back(instr.first);
		}
		else if (instr.second == "INVALID") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::INVALID));
			ends.push_back(instr.first);
		}
		else if (instr.second == "SELFDESTRUCT") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::SELFDESTRUCT));
			ends.push_back(instr.first);
		}
		else if (instr.second == "STOP") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::STOP));
			ends.push_back(instr.first);
		}
		else if (instr.second == "RETURN") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::RETURN));
			ends.push_back(instr.first);
		}
		else if (instr.second == "REVERT") {
			blockEndInfo.insert(pair<int, BlockType>(instr.first, BlockType::REVERT));
			ends.push_back(instr.first);
		}
		else if (boost::starts_with(instr.second, "tag") && blockEndInfo.find(preInstrAddr) == blockEndInfo.end()) {
			blockEndInfo.insert(pair<int, BlockType>(preInstrAddr, BlockType::NATURAL));//should add the block before JUMPDEST block
			ends.push_back(preInstrAddr);
		}
		preInstrAddr = instr.first;
	}

	int start = 0;
	for (auto& end : ends) {
		map<int, string> instrs;
		auto i = instructions.find(start);
		for (; i != instructions.find(end); i++)
			instrs.insert(pair<int, string>(i->first, i->second));
		instrs.insert(make_pair(i->first, i->second));
		i++;

		EBasicBlock bb(start, end, blockEndInfo[end], instrs);
		//displayRedMsg(to_string(start) + "-" + to_string(end) + " : " + to_string(blockEndInfo[end]));
		blocks.insert(pair<int, EBasicBlock>(start, bb));

		if (i != instructions.end())
			start = i->first;
	}
}

void delUnreachableBlocks(map<int, string>& instrs) {
	map<int, EBasicBlock> blocks;
	genBasicBlocks(instrs, blocks);
	map<int, int> tagNum2Addr;
	for (auto& bb : blocks)
		if (boost::starts_with(instrs.at(bb.first), "tag")) {
			int tagNum = stoi(instrs.at(bb.first).substr(3));
			assert(tagNum2Addr.find(tagNum) == tagNum2Addr.end());
			tagNum2Addr.insert(make_pair(tagNum, bb.first));
		}

	stackKeys.clear();
	map<int, vector<string>> blockChanges;
	map<int, int> blockMinDepth;
	map<int, string> blockNext;
	for (auto& bb : blocks)
		genTagStackChanges(bb.second, blockChanges, blockMinDepth, blockNext, tagNum2Addr);
	vector<string>stack;
	set<int> blockVisited;
	traverseTagBlocks(blocks, 0, stack, blockChanges, blockMinDepth, blockNext, blockVisited);
	set<int> delBlocks;
	set<int> delInstrs;
	for (auto& bb : blocks)
		if (blockVisited.find(bb.first) == blockVisited.end()) {
			delBlocks.insert(bb.first);
			for (auto& i : blocks.at(bb.first).getInstrs())
				delInstrs.insert(i.first);
		}

	cout << "deleted blocks : ";
	for (auto d : delBlocks)
		cout << d << " ";
	cout << endl;

	for (auto& i : delInstrs)
		instrs.erase(i);
}

//runtimeNodes 构造的CFG的所有节点
//allReInvAddrs 检测出冗余的所有INVALID地址
//inivIDs 所有冗余INVALID节点ID
//jumpInfoIDMaps 经过修正的jumpInfo和Node ID的映射关系
//functions 函数体的起始地址 => 终止地址
//instrs 地址=> 指令
//invRelatedInstrStart INVALID地址 => 冗余字节码序列的起始地址
//pushTags 所有push地址的PUSHx指令地址
void optimize(const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& edges, const map<int, EBasicBlock>& blocks, const set<int>& allReInvAddrs, const set<int>& invIDs, const map<int, map<int, tuple<int, int>>>& IDAddrs, const map<int, map<int, int>>& funcEnds, const map<int, map<int, vector<int>>>& funcTopLevelIDs, const map<int, string>& instrs, const map<int, int>& invRelatedInstrStart, const map<int, int>& invTypes, const set<int>& JUMPDESTs,
	const map<int, int>& push2JumpMap,
	const string& contractName,
	map<int, string>& optimizedInstrs,
	const map<int, BlockInstrsChanges*>& block2InstrChanges, const map<int, BlockInstrsChanges*>& nodeID2Changes, const set<int>& sloadPartReIDs,
	const map<int, int>& codecopyBlocks, const map<int, int>& codecopyOffsetInstrs, const map<int, int>& codecopySizeInstrs, int preCleanRuntimeSize, map<int, int>& oldCodeCopyAddr2NewOffset) {


	//较为诡异的是，字节码序列中可能存在部分JUMPDEST没有对应的push tag
	//以上这种JUMPDEST竟然是通过指令Fall的方式遍历而不是通过JUMP的方式遍历
	//即pushTags数少于JUMPDESTs数
	map<int, int> originalTags;//JUMPDEST addr => tagNum
	for (auto& push : push2JumpMap) {
		vector<string> temp;
		boost::split(temp, instrs.at(push.first), boost::is_any_of(" "));
		int pushValue;
		SSCANF(temp[1].c_str(), "%x", &pushValue);
		if (originalTags.find(pushValue) == originalTags.end())
			originalTags.insert(make_pair(pushValue, genNewTagCnt()));
	}

	//将没有push tag对应的JUMPDEST也应该赋一个tag值
	for (auto& jst : JUMPDESTs)
		if (originalTags.find(jst) == originalTags.end())
			originalTags.insert(make_pair(jst, genNewTagCnt()));

	set<int> partReInvAddrs;//部分冗余的invalid地址
	set<int> absReInvAddrs;//完全冗余的invalid 地址
	for (auto& n : runtimeNodes) {
		if (n.second.getBlockType() == BlockType::INVALID) {
			int invAddr = n.second.getStart();
			if (partReInvAddrs.find(invAddr) == partReInvAddrs.end() && invIDs.find(n.first) == invIDs.end())
				partReInvAddrs.insert(invAddr);
		}
	}
	set_difference(allReInvAddrs.begin(), allReInvAddrs.end(), partReInvAddrs.begin(), partReInvAddrs.end(), inserter(absReInvAddrs, absReInvAddrs.end()));
	partReInvAddrs.clear();
	set_difference(allReInvAddrs.begin(), allReInvAddrs.end(), absReInvAddrs.begin(), absReInvAddrs.end(), inserter(partReInvAddrs, partReInvAddrs.end()));

	//resultInstrs删除绝对冗余的invlid指令
	map<int, int> allReInvRelatedInstrStart;//绝对冗余的invalid指令对应的冗余序列起始地址
	for (auto& i : absReInvAddrs)
		allReInvRelatedInstrStart.insert(make_pair(i, invRelatedInstrStart.at(i)));
	map<int, string> resultInstrs = instrs;
	
	set<int>deInstrs;
	map<int, string> changeInstrs;
	for (auto& i : allReInvRelatedInstrStart) {
		auto begin = resultInstrs.find(i.second);
		auto end = resultInstrs.find(i.first);
		if (invTypes.at(i.first) == 1)
			end++;
		else if (invTypes.at(i.first) == 2) {
			end--;//INVALID =>JUMPI
			changeInstrs.insert(make_pair(end->first, "JUMP"));
			end--;//JUMPI => PUSH addr
			end--;//PUSH addr => delete end
			deInstrs.insert(i.first);
		}
		while (begin != end) {
			deInstrs.insert(begin->first);
			begin++;
		}
		deInstrs.insert(end->first);
	}

	for (auto& b : block2InstrChanges) {
		for (auto& i : b.second->deInstrs)
			deInstrs.insert(i);
		for (auto& c : b.second->updateInstrs)
			changeInstrs.insert(c);
	}

	for (auto& i : deInstrs)
		resultInstrs.erase(i);
	for (auto& i : changeInstrs)
		resultInstrs.at(i.first) = i.second;

	generateOriginalTagInstrs(contractName + ".originalTagInstr.runtime", resultInstrs, originalTags, push2JumpMap);

	set<int> partReIDs;//部分冗余的所有节点ID
	for (auto& id : invIDs)
		if (absReInvAddrs.find(runtimeNodes.at(id).getStart()) == absReInvAddrs.end())
			partReIDs.insert(id);

	//由于同一ID不可能同时为冗余SLOAD所在节点和INVALID节点，因此可以同时处理
	for (auto& id : sloadPartReIDs)
		partReIDs.insert(id);

	//生成每个部分冗余节点的调用链
	//首先针对每个部分冗余节点生成一条路径
	//然后针对每条部分分析其函数调用链
	map<int, vector<int>> paths;
	getDstIDPaths(edges, partReIDs, paths);

	//同一个ID可能有不同的函数调用方式
	//具体可查看 0xc09315c63f477ba1e15120d2b3a43f109eea9787
	//其中Node_59有两种调用链
	//Node_61 => Node_49 => Node_59
	//Node_33 => Node_49 => Node_59
	map<int, set<vector<int>>> id2AddrCallChains;//ID(冗余INVALID、SLOAD) => 函数调用链的地址
	map<int, set<vector<int>>> id2IDCallChains;//ID(冗余INVALID、SLOAD) => 函数调用链ID
	//以下仅需要处理部分冗余的节点，即处理调用链
	map<vector<int>, set<vector<int>>> callChainGraph;
	map<int, int> jumpInTgts;
	for (auto& id : partReIDs) {
		//const vector<int>& jumpInfo = runtimeNodes.at(id).getJumpInfo();
		vector<int> jumpInfo;
		vector<int> jumpIDInfo;

		//这里仅仅生成一条可能的调用链
		genCallChain(id, paths.at(id), runtimeNodes, IDAddrs, funcEnds, jumpInfo, jumpIDInfo);

		//0x3528C164e3fCA20E2333Cf58Ab4B1c99DeF83347 出现的诡异情况
		//0x7712f76d2a52141d44461cdbc8b660506dcab752 同上
		//或者可以这样理解，由于我们的函数构造方式是通过查看相同的子图
		//子图的定义是所有以起始基本块生成的CFG Node开始构造的一块完全相同的地址跳转图
		//jumpInfo.size() == 1表明我们找不到两个子图去覆盖INVALID节点
		//此时的INVALID节点不属于任一函数体，该现象的出现大致原因在于中转块的存在使得不同函数体之间出现了交集
		if (jumpInfo.size() == 1)
			continue;

		vector<int> funcStartIDs;
		vector<int> jumpIns = jumpIDInfo;
		jumpIns.pop_back();
		for (auto& in : jumpIns)
			funcStartIDs.push_back(runtimeNodes.at(in).getJumpID());
		vector<set<int>> jumpInIDs;
		for (auto& s : funcStartIDs) {
			set<int> jumps;
			jumps = runtimeNodes.at(s).getParents();
			jumpInIDs.push_back(jumps);
			for (auto& j : jumps)
				jumpInTgts.insert(make_pair(runtimeNodes.at(j).getEnd(), runtimeNodes.at(s).getStart()));
		}
		vector<vector<int>> chains;//id的所有调用链，以下两个for循环是处理每层调用时可能出现的多个JUMP [in] Node
		for (auto& i : jumpInIDs[0]) {
			vector<int> first = { i };
			chains.push_back(first);
		}
		for (size_t i = 1; i < jumpInIDs.size(); i++) {
			size_t preSize = chains.size();
			auto iter = jumpInIDs[i].begin();
			for (size_t j = 0; j < preSize; j++)
				chains[j].push_back(*iter);
			iter++;
			for (; iter != jumpInIDs[i].end(); iter++) {
				for (size_t k = 0; k < preSize; k++) {
					chains.push_back(chains[k]);
					chains.back().back() = *iter;
				}
			}
		}

		for (auto& c : chains) {
			vector<int> addrChains;
			for (auto& chainid : c)
				//注意输出的是跳转地址，所以是基本块末尾地址
				addrChains.push_back(runtimeNodes.at(chainid).getEnd());

			//SLOAD块应该用起始地址
			//INVALID块的起始地址和终止地址相同，所以也可以用起始地址
			addrChains.push_back(runtimeNodes.at(id).getStart());

			c.push_back(id);
			id2IDCallChains[id].insert(c);

			id2AddrCallChains[id].insert(addrChains);
		}
		//displayRedMsg(to_string(id));
		//for (auto& c : id2IDCallChains.at(id)) {
		//	displayBlueMsg("ID Chain");
		//	for (auto& id : c)
		//		cout << id << " ";
		//	cout << endl;
		//}
		//for (auto& c : id2AddrCallChains.at(id)) {
		//	displayGreenMsg("ADDR Chain : ");
		//	for (auto& id : c)
		//		cout << id << " ";
		//	cout << endl;
		//}



		//注意这里使用的时函数调用链的地址，这是因为我们假设在一个调用链中同一个jump [in]只会出现一次（否则会出现递归的情况），所以用在一条调用链中不会出现地址混淆的情况
		assert(jumpInfo.size() >= 2);
		for (auto& infos : id2AddrCallChains)
			for (auto& jumpInfo : infos.second) {
				for (size_t i = 1; i < jumpInfo.size(); i++) {

					vector<int> pnt(jumpInfo.begin(), jumpInfo.begin() + i);
					vector<int> chd(jumpInfo.begin(), jumpInfo.begin() + i + 1);
					callChainGraph[pnt].insert(chd);
				}
				callChainGraph[jumpInfo] = {};
			}
	}

	//由于冗余Sload的优化需要具体NodeID的优化信息，所以需要将函数调用链对应到ID
	map<vector<int>, int> addrCallChain2ID;
	for (auto& id : id2AddrCallChains)
		for (auto& chain : id.second)
			addrCallChain2ID[chain] = id.first;

	genCallChainDotFile(callChainGraph, addrCallChain2ID, runtimeNodes, contractName + ".invcallgraph.dot");

	vector<vector<int>> chainTraverseOrder;
	set<vector<int>> visited;
	for (auto& chain : callChainGraph) {
		if (chain.first.size() != 1)
			continue;
		queue<vector<int>> que;
		que.push(chain.first);
		while (!que.empty()) {
			const vector<int>& front = que.front();
			chainTraverseOrder.push_back(front);
			for (auto& chd : callChainGraph.at(front)) {
				if (visited.find(chd) == visited.end()) {
					que.push(chd);
					visited.insert(chd);
				}
			}
			que.pop();
		}
	}

	//for (auto iter = chainTraverseOrder.rbegin(); iter != chainTraverseOrder.rend(); iter++)
	//	displayIntVector(*iter);

	unordered_map<FuncBody, int, FuncBodyHash> optimizedFuncBodys;
	map<vector<int>, FuncBody*> chainFuncBodys;

	//生成优化需要的所有函数体的结构信息：需要删除的INVALID地址、需要改变的JUMP in地址以及对应的跳转函数体
	for (auto iter = chainTraverseOrder.rbegin(); iter != chainTraverseOrder.rend(); iter++) {
		if (!callChainGraph.at(*iter).empty()) {
			int funcStart = -1;
			if ((*iter).size() != 1) {
				//funcStart = getInstrFuncStart((*iter).back(), start2End);
				int jumpInAddr = (*iter)[(*iter).size() - 2];
				funcStart = jumpInTgts.at(jumpInAddr);
			}


			FuncBody* chdFb = new FuncBody(-1);
			for (auto& chd : callChainGraph.at(*iter)) {
				if (chdFb->funcStart == -1) {
					chdFb->funcStart = jumpInTgts.at(chd[chd.size() - 2]);
					//chdFb->funcStart = getInstrFuncStart(chd.back(), start2End);
				}
				if (callChainGraph.at(chd).empty()) {//此时chd.back()不一定是INVALID节点，但此时chd调用链对应的一定是某一节点（冗余SLOAD节点或者INVALID节点）
					if(instrs.at(chd.back()) == "INVALID")
						chdFb->delInvs.insert(chd.back());
					else {
						int id = addrCallChain2ID.at(chd);
						chdFb->sloadRelChanges.insert(make_pair(runtimeNodes.at(id).getStart(), nodeID2Changes.at(id)));
					}
				}
				else for (auto& j : chainFuncBodys.at(chd)->jumpIns)
					chdFb->jumpIns.insert(make_pair(j.first, j.second));
			}

			if (optimizedFuncBodys.find(*chdFb) == optimizedFuncBodys.end())
				optimizedFuncBodys.insert(make_pair(*chdFb, genNewTagCnt()));

			FuncBody* fb = new FuncBody(funcStart);
			fb->jumpIns.insert(make_pair((*iter).back(), chdFb));

			chainFuncBodys.insert(make_pair(*iter, fb));

			if (optimizedFuncBodys.find(*fb) == optimizedFuncBodys.end())
				optimizedFuncBodys.insert(make_pair(*fb, genNewTagCnt()));
		}
	}

	//未优化前的CODECOPY指令地址 =》优化后的指令序列resultInstrs中的与该CODECOPY指令相关的push offset指令的新地址
	//如果是原指令序列中的指令，则不变
	//如果是新生成的指令，则需要进行确认
	map<int, int> newpushOffsetAddr2oldcodecopyAddr;

	//生成需要添加的函数体
	int instrStart = resultInstrs.rbegin()->first + 1;
	map<int, string> newInstrs;
	unordered_set<FuncBody, FuncBodyHash> generated;

	//函数调用链最外面一层的跳转地址对应的跳转函数体的起始地址tag
	map<int, int> jump2tagNums;
	map<int, map<int, int>> funcBlockNums;//记录每个函数体所包含的所有基本块及其个数
	for (auto& b : chainFuncBodys) {
		if (b.first.size() == 1) {
			assert(b.second->delInvs.empty());
			assert(b.second->jumpIns.size() == 1);

			queue<FuncBody*> que;
			FuncBody* root = b.second->jumpIns.begin()->second;
			jump2tagNums.insert(make_pair(b.first[0], optimizedFuncBodys.at(*root)));
			if (generated.find(*root) == generated.end()) {
				generated.insert(*root);
				que.push(root);
			}
			while (!que.empty()) {
				const FuncBody* front = que.front();
				genFuncBodyInstrs(*front, resultInstrs, blocks, IDAddrs, push2JumpMap, instrStart, invRelatedInstrStart, invTypes, optimizedFuncBodys, newInstrs, originalTags, funcBlockNums, codecopyOffsetInstrs, newpushOffsetAddr2oldcodecopyAddr);
				for (auto& jmp : front->jumpIns)
					if (generated.find(*(jmp.second)) == generated.end()) {
						generated.insert(*(jmp.second));
						que.push(jmp.second);
					}
				que.pop();
			}
		}
	}

	for (auto& i : resultInstrs) {
		if (i.second == "JUMPDEST")
			i.second = "tag " + to_string(originalTags.at(i.first));
		else if (i.second.find("PUSH") != string::npos && push2JumpMap.find(i.first) != push2JumpMap.end()) {
			int tagNum = -1;

			//这里的jump2tagNums记录的是部分冗余的assertion节点的函数调用链的最外层调用地址
			//比如说：jmp_addr1->jmp_addr2->jmp_addr3->inv_addr
			//这个最外层地址jmp_addr1应该调整为指向jmp_addr2所在的新函数体
			if (jump2tagNums.find(push2JumpMap.at(i.first)) == jump2tagNums.end()) {
				vector<string> temp;
				boost::split(temp, i.second, boost::is_any_of(" "));
				int addr = -1;
				SSCANF(temp[1].c_str(), "%x", &addr);
				tagNum = originalTags.at(addr);
			}
			else
				tagNum = jump2tagNums.at(push2JumpMap.at(i.first));

			assert(tagNum != -1);
			i.second = "push tag " + to_string(tagNum);
		}
		else if (i.second == "CODECOPY") {
			//runtime部分一般只需要改动偏移量，不会改变size的
			assert(codecopyOffsetInstrs.find(i.first) != codecopyOffsetInstrs.end());
			int offsetPushAddr = codecopyOffsetInstrs.at(i.first);
			assert(resultInstrs.find(offsetPushAddr) != resultInstrs.end());
			newpushOffsetAddr2oldcodecopyAddr.insert(make_pair(offsetPushAddr, i.first));
		}
	}

	int pushTagNum = 0;
	size_t otherInstrsSize = 0;
	resultInstrs.insert(newInstrs.begin(), newInstrs.end());

	//由于优化和push addr指令的不确定性，干脆在生成新函数体，并且改变了最外层调用的函数体后，进行遍历，看哪些基本块没有被遍历过，然后直接删除即可，之前的各种方式确认能被删除的基本块很难做到该删的都删，不该删的都没删
	Contract::generateDisasm(resultInstrs, contractName + ".temp.re.tagInstrs.runtime");
	delUnreachableBlocks(resultInstrs);
	//Contract::generateDisasm(resultInstrs, contractName + ".temp.tagInstrs.runtime");


	map<int, tuple<int, size_t>> addr2TagNumAndInstrsSize;//resInstrs的每个临时地址对应于在该指令之前的所有push tag数量以及已存在的指令序列的大小
	map<int, int> tagNum2Addr;
	for (auto& i : resultInstrs) {
		addr2TagNumAndInstrsSize[i.first] = make_tuple(pushTagNum, otherInstrsSize);
		//addr2TagNumAndInstrsSize.insert(make_pair(i.first, make_tuple(pushTagNum, otherInstrsSize)));
		assert(i.second != "JUMPDEST");
		if (i.second.find("push") != string::npos)
			pushTagNum++;
		else if (i.second.find("PUSH") != string::npos) {

			vector<string> temp;
			boost::split(temp, i.second, boost::is_any_of(" "));
			otherInstrsSize += temp[1].size() / 2;
		}
		else if(isLowercaseHex(i.second)){
			otherInstrsSize += i.second.size() / 2;
		}
		else {
			if (i.second.find("tag") != string::npos) {
				vector<string> temp;
				boost::split(temp, i.second, boost::is_any_of(" "));
				int tagNum = stoi(temp[1]);
				assert(tagNum2Addr.find(tagNum) == tagNum2Addr.end());
				tagNum2Addr.insert(make_pair(tagNum, i.first));
			}
			otherInstrsSize++;
		}
	}

	int addrSize = 1;
	int start = 256;
	while (true) {
		if (otherInstrsSize + pushTagNum * (addrSize + 1) <= start)
			break;
		start *= 256;
		addrSize++;
	}

	int newSize = int(otherInstrsSize + pushTagNum * (addrSize + 1));//16进制字符串的长度


	for (auto& i : resultInstrs) {
		const tuple<int, size_t>& tle = addr2TagNumAndInstrsSize.at(i.first);
		int addr = get<0>(tle) * (addrSize + 1) + int(get<1>(tle));
		string opcode;
		if (i.second.find("push") != string::npos) {
			vector<string> temp;
			boost::split(temp, i.second, boost::is_any_of(" "));
			int tagNum = stoi(temp[2]);
			opcode += "PUSH" + to_string(addrSize);
			const tuple<int, size_t>& t = addr2TagNumAndInstrsSize.at(tagNum2Addr.at(tagNum));
			int pushValue = get<0>(t) * (addrSize + 1) + int(get<1>(t));
			stringstream ss;
			ss << hex << pushValue;
			string pushStr;
			ss >> pushStr;
			string zero;
			for (size_t i = pushStr.size(); i < addrSize * 2; i++)
				zero.push_back('0');
			pushStr = zero + pushStr;
			opcode += " 0x" + pushStr;
			optimizedInstrs.insert(make_pair(addr, opcode));
		}
		else if (i.second.find("tag") != string::npos) {
			opcode = "JUMPDEST";
			optimizedInstrs.insert(make_pair(addr, opcode));
		}
		else if (newpushOffsetAddr2oldcodecopyAddr.find(i.first) != newpushOffsetAddr2oldcodecopyAddr.end()) {
			if (i.second == "CODESIZE") {
				opcode = i.second;
			}
			else {
				assert(i.second.find("PUSH") != string::npos);
				vector<string> temp;
				boost::split(temp, i.second, boost::is_any_of(" "));
				int pushSize = stoi(temp[0].substr(4));
				string pushX = temp[0];
				//由于我们生成新函数体指令的时候是完全复制之前的指令的，所以新的push offset指令和之前的push offset应该一致
				//为了保险起见，我们这里加了assertion
				int oldCodecopyAddr = newpushOffsetAddr2oldcodecopyAddr.at(i.first);
				int oldOffsetAddr = codecopyOffsetInstrs.at(oldCodecopyAddr);
				string oldOffsetInstr = instrs.at(oldOffsetAddr);
				assert(oldOffsetInstr == i.second);
				temp.clear();
				boost::split(temp, oldOffsetInstr, boost::is_any_of(" "));
				int oldOffset = -1;
				SSCANF(temp[1].c_str(), "%x", &oldOffset);

				int newOffset = newSize - preCleanRuntimeSize + oldOffset;
				oldCodeCopyAddr2NewOffset.insert(make_pair(oldCodecopyAddr, newOffset));

				stringstream ss;
				ss << hex << newOffset;
				string newOffsetHexStr;
				ss >> newOffsetHexStr;
				assert(newOffsetHexStr.length() <= pushSize * 2);
				for (int i = (int)newOffsetHexStr.length(); i < pushSize * 2; i++)
					newOffsetHexStr = "0" + newOffsetHexStr;

				opcode = pushX + " " + "0x" + newOffsetHexStr;
			}
			optimizedInstrs.insert(make_pair(addr, opcode));
		}
		else if (isLowercaseHex(i.second)) {
			for (size_t idx = 0; idx < i.second.length();) {
				string opcode = "";
				size_t temp = idx;
				string bytecode = i.second.substr(temp, 2);
				temp += 2;
				string mnemonic = Opcode::getMnemonics(stoi(bytecode, nullptr, 16));
				opcode.append(mnemonic);
				if (mnemonic.find("PUSH") != string::npos) {
					int size = atoi(mnemonic.substr(4).c_str()) * 2;
					string pushValue = "0x" + i.second.substr(temp, size);
					temp += size;
					opcode.append(" " + pushValue);
				}
				optimizedInstrs.insert(make_pair(addr, opcode));
				addr += int(temp - idx) / 2;
				idx = temp;
			}
		}
		else {
			opcode = i.second;
			optimizedInstrs.insert(make_pair(addr, opcode));
		}
	}

	Contract::generateDisasm(optimizedInstrs, contractName + ".optimize.runtime");
}

void genBytecode(const map<int, string>& instrs, string& bytecode) {
	for (auto& i : instrs) {
		vector<string> temp;
		boost::split(temp, i.second, boost::is_any_of(" "));
		int opcode = Opcode::getOpcode(temp[0]);
		stringstream ss;
		ss << hex << opcode;
		string hexOp;
		ss >> hexOp;
		if (hexOp.length() == 1)
			hexOp = "0" + hexOp;
		bytecode += hexOp;
		if (temp.size() > 1)
			bytecode += temp[1].substr(2);
	}
}