#include "Contract.h"
#include <list>
#include <queue>

void displayRedMsg(const std::string& s, spdlog::level::level_enum level);
void displayBlueMsg(const std::string& s, spdlog::level::level_enum level);
void displayGreenMsg(const std::string& s, spdlog::level::level_enum level);
void displayYellowMsg(const std::string& s, spdlog::level::level_enum level);
void displayPurpleMsg(const std::string& s, spdlog::level::level_enum level);
void displayCyanMsg(const std::string& s, spdlog::level::level_enum level);

void testSCC(const map<int, set<int>>& edges, map<int, set<int>>& scc, const set<int>& jmpiTgt, const set<int>& natTgt, const map<int, ECFGNode>& nodes);
void generateInvalidDotGraph(const map<int, ECFGNode>& nodes, string fileName, const map<int, set<int>>& edges);
void parallelSolve(const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt, set<int>& loopInvalids, vector<int>& redundantInvs);
void isRedundant(const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt, vector<int>& IDs, const string& name);
map<int, int> getInvRelatedInstrsStart(const set<int>& invAddrs, const map<int, set<int>>& edges, map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt);
void pruningInvalids(const map<int, ECFGNode>& nodes, map<int, set<int>>& edges);

void genBytecode(const map<int, string>& instrs, string& bytecode);

void optimize(const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& edges, const map<int, EBasicBlock>& blocks, const set<int>& allReInvAddrs, const set<int>& invIDs, const map<int, map<int, tuple<int, int>>>& IDAddrs, const map<int, map<int, int>>& funcEnds, const map<int, map<int, vector<int>>>& funcTopLevelIDs, const map<int, string>& instrs, const map<int, int>& invRelatedInstrStart, const map<int, int>& invTypes, const set<int>& JUMPDESTs,
	const map<int, int>& push2JumpMap,
	const string& contractName,
	map<int, string>& optimizedInstrs,
	const map<int, BlockInstrsChanges*>& block2InstrChanges, const map<int, BlockInstrsChanges*>& nodeID2Changes, const set<int>& sloadPartReIDs,
	const map<int, int>& codecopyBlocks, const map<int, int>& codecopyOffsetInstrs, const map<int, int>& codecopySizeInstrs, int preCleanRuntimeSize, map<int, int>& oldCodeCopyAddr2NewOffset);

void displayStack(const vector<int>& stack) {
	for (auto i = stack.rbegin(); i != stack.rend(); i++)
		cout << (*i) << " ";
	cout << endl;
}

int Contract::getOpcodeSize(string opcode) {
	if (opcode.find("PUSH") != string::npos)
		return atoi(opcode.substr(4, opcode.find(" ") - 4).c_str()) + 1;
	else
		return 1;
}
void Contract::genInstrs(const string& bytecodes, map<int, string>& instrs) {
	for (size_t i = 0; i < bytecodes.length();) {
		string opcode = "";
		size_t temp = i;
		string bytecode = bytecodes.substr(temp, 2);
		temp += 2;
		string mnemonic;
		if (Opcode::exists(stoi(bytecode, nullptr, 16)))
			mnemonic = Opcode::getMnemonics(stoi(bytecode, nullptr, 16));
		else
			mnemonic = "Missing Opcode 0x" + bytecode;
		opcode.append(mnemonic);
		if (mnemonic.find("PUSH") != string::npos) {
			int size = atoi(mnemonic.substr(4).c_str()) * 2;
			if (size_t(temp) + size_t(size)/* avoid add overflow,so cast to a wider type before add*/ >= bytecodes.length()) {
				//cerr << "incomplete push instruction at " << (i / 2) << endl;
				break;
			}
			else {
				string pushValue = "0x" + bytecodes.substr(temp, size);
				temp += size;
				opcode.append(" " + pushValue);
			}
		}
		instrs.insert(pair<int, string>(int(i) / 2, opcode));//two hex-bits represent 1 byte
		i = temp;
	}
}
void Contract::genInstrSrcmap(const string& stringMap, map<int, string>& instrs, map<int, vector<string>>& instrMaps) {
	vector<string> preMaps;//pre process map
	boost::split(preMaps, stringMap, boost::is_any_of(";"));

	vector<string> mapInfo;
	//s:l:f:j:m
	//s : the byte-offset to the start of the range in the source file
	//l : the length of the source range in bytes
	//f : the source file index mentioned above(may be -1)
	//j : jump info "i" "o" "-"
	//m(newer solc version) : is an integer that denotes the “modifier depth”(目前在0.6.3版本可见)
	boost::split(mapInfo, preMaps[0], boost::is_any_of(":"));

	size_t infoSize = mapInfo.size();

	vector<vector<string>> mapInfos;
	mapInfos.push_back(mapInfo);

	vector<string> preInfo = mapInfo;//previous map info
	for (size_t i = 1; i < preMaps.size(); i++) {
		vector<string> temp;
		boost::split(temp, preMaps[i], boost::is_any_of(":"));
		for (size_t j = 0; j < temp.size(); j++)
			if (temp[j] == "")temp[j] = preInfo[j];
		for (size_t j = temp.size(); j < infoSize; j++)
			temp.push_back(preInfo[j]);

		mapInfos.push_back(temp);
		preInfo = temp;
	}

	int i = 0;
	for (map<int, string>::iterator iter = instrs.begin(); iter != instrs.end();) {
		if (i >= mapInfos.size()) {
			iter = instrs.erase(iter);
		}
		else {
			instrMaps[iter->first] = mapInfos[i];
			iter++;
		}
		i++;
	}
}

void Contract::genBasicBlocks(const map<int, string>& instructions, map<int, EBasicBlock>& blocks) {
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
		else if (instr.second == "JUMPDEST" && blockEndInfo.find(preInstrAddr) == blockEndInfo.end()) {
			blockEndInfo.insert(pair<int, BlockType>(preInstrAddr, BlockType::NATURAL));//should add the block before JUMPDEST block
			ends.push_back(preInstrAddr);
		}
		preInstrAddr = instr.first;
	}

	int start = 0;
	for (auto& end : ends) {
		map<int, string> instrs;
		for (int i = start; i <= end;) {
			instrs.insert(pair<int, string>(i, instructions.at(i)));
			i += getOpcodeSize(instructions.at(i));
		}
		//assert(blockEndInfo.find(end) != blockEndInfo.end());
		EBasicBlock bb(start, end, blockEndInfo[end], instrs);

		//console->debug(to_string(start) + "-" + to_string(end) + " : " + to_string(blockEndInfo[end]));
		//displayRedMsg(to_string(start) + "-" + to_string(end) + " : " + to_string(blockEndInfo[end]));
		blocks.insert(pair<int, EBasicBlock>(start, bb));

		start = end + getOpcodeSize(instructions.at(end));
	}
}

void pushInstr(int bytecode, string value, int addrSize, vector<string>& stack, const set<int>& JUMPDESTs) {
	if (bytecode - 0x60 + 1 == addrSize) {
		int addr = -1;
		SSCANF(value.c_str(), "%x", &addr);
		//assert(addr != -1);
		if (JUMPDESTs.find(addr) != JUMPDESTs.end()) {
			stack.push_back("-" + value);
		}
		else {
			stack.push_back("1");
		}
	}
	else {
		stack.push_back("1");
	}
}

void pushAddr(int pc, int bytecode, string value, int addrSize, vector<string>& tagStack, const set<int>& JUMPDESTs) {
	if (bytecode - 0x60 + 1 == addrSize) {
		int addr = -1;
		SSCANF(value.c_str(), "%x", &addr);
		//assert(addr != -1);
		if (JUMPDESTs.find(addr) != JUMPDESTs.end()) {
			tagStack.push_back("-" + to_string(pc));
		}
		else {
			tagStack.push_back("1");
		}
	}
	else {
		tagStack.push_back("1");
	}
}

void Contract::genStackChanges(const EBasicBlock& bb, const int& addrSize, const set<int>& JUMPDESTs) {
	vector<string> testStack;
	//s1023,s1022,...,s1,s0
	//之所以选1024是因为solidity的默认栈最大深度为1024
	const int MAXDEPTH = 1024;
	for (int i = MAXDEPTH - 1; i >= 0; i--)
		testStack.push_back("s" + to_string(i));
	vector<string> testTagStack = testStack;
	//string target = "-1";
	int curDepth = 0;
	int minDepth = 0;
	vector<string> tgt;
	for (auto& i : bb.getInstrs()) {
		tgt = instrSim(i.first, i.second, testStack, testTagStack, addrSize, JUMPDESTs, curDepth, minDepth);

		//displayGreenMsg(to_string(i.first) + " " + i.second);
		//for (int i = 1024 + minDepth; i < testStack.size(); i++)
		//	cout << testStack[i] << " ";
		//cout << " : TOP" << endl;
		//string dep = "curDepth : " + to_string(curDepth) + ", minDepth : " + to_string(minDepth);
		//displayRedMsg(dep);
	}

	blockChanges[bb.getStart()] = { };
	tagChanges[bb.getStart()] = { };
	assert(testStack.size() == testTagStack.size());
	for (int i = MAXDEPTH + minDepth; i < testStack.size(); i++) {
		blockChanges.at(bb.getStart()).push_back(testStack[i]);
		tagChanges.at(bb.getStart()).push_back(testTagStack[i]);
	}
	blockChangedDepth.insert(make_pair(bb.getStart(), curDepth));
	blockMinDepth.insert(make_pair(bb.getStart(), minDepth));
	blockNext.insert(make_pair(bb.getStart(), tgt[0]));
	pushTagIdx.insert(make_pair(bb.getStart(), tgt[1]));
}

void Contract::genPushTags(const map<int, ECFGNode>& nodes, int ID, vector<string>& stack, const int& addrSize, const set<int>& JUMPDESTs, set<int>& pushTags, map<int, int>& push2JumpMap, set<vector<string>>& IDVisited) {
	vector<string> stackKey = stack;
	stackKey.push_back(to_string(ID));
	//由于优化的原因，可能同一个Node ID会有多个JUMP [in]的父节点
	//为了得到所有父节点中的pushTag信息，需要依据遍历到该节点时的栈中内容不同（一般情况下是不同的地址push相同的内容）对该节点进行多次遍历
	IDVisited.insert(stackKey);
	int curBlock = nodes.at(ID).getStart();
	const EBasicBlock& bb = blocks.at(curBlock);
	vector<string> change = tagChanges.at(curBlock);
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

	string pushTag = pushTagIdx.at(curBlock);
	int target = -1;
	if (pushTag[0] == 's') {
		size_t lastIdx = stoi(pushTag.substr(1));
		SSCANF(stack[stack.size() - 1 - lastIdx].substr(1).c_str(), "%d", &target);
	}
	else
		SSCANF(pushTag.substr(1).c_str(), "%d", &target);

	vector<string> dupStack = after;
	int jumpID = nodes.at(ID).getJumpID();
	int fallsID = nodes.at(ID).getFallsID();
	if (jumpID != -1) {
		pushTags.insert(target);
		push2JumpMap.insert(make_pair(target, nodes.at(ID).getEnd()));

		vector<string> jumpStackKey = after;
		jumpStackKey.push_back(to_string(jumpID));
		if (IDVisited.find(jumpStackKey) == IDVisited.end())
			genPushTags(nodes, jumpID, after, addrSize, JUMPDESTs, pushTags, push2JumpMap, IDVisited);
	}
	if (fallsID != -1) {
		vector<string> fallsStackKey = dupStack;
		fallsStackKey.push_back(to_string(fallsID));
		if (IDVisited.find(fallsStackKey) == IDVisited.end())
			genPushTags(nodes, fallsID, dupStack, addrSize, JUMPDESTs, pushTags, push2JumpMap, IDVisited);
	}

}

void instrCODECOPYSim(int pc, string instr, vector<int>& stack) {
	vector<string> instrParts;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string& opcode = instrParts[0];
	int bytecode = Opcode::getOpcode(opcode);
	int before = int(stack.size());
	switch (bytecode) {
	case 0x38: {//CODESIZE
		stack.push_back(-pc);
		break;
	}
	case 0x57: {//JUMPI
		stack.pop_back(); stack.pop_back();
		break;
	}
	case 0x56: {//JUMP
		stack.pop_back();
		break;
	}
	case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
	case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
		//PUSHx
		stack.push_back(-pc);
		break;
	}
	case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
		//DUPx
		size_t index = atoi(opcode.substr(3).c_str());//index : 1~16
		stack.push_back(stack[stack.size() - index]);
		break;
	}
	case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
		//SWAPx
		size_t index = atoi(opcode.substr(4).c_str());//index : 1~16
		size_t size = stack.size();
		int temp = stack.back();
		stack[size - size_t(1)] = stack[size - index - 1];
		stack[size - index - 1] = temp;
		break;
	}
	case 0x16:case 0x17: case 0x18:case 0x03:case 0x04:case 0x1b:case 0x1c: {
		//AND OR XOR SUB DIV SHL SHR
		stack.pop_back();
		stack.pop_back();
		stack.push_back(1);
		break;
	}
	case 0x01:case 0x02: {
		//ADD MUL
		stack.pop_back();
		stack.pop_back();
		stack.push_back(1);
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
			stack.push_back(1);
		}
		break;
	}
	}
	int after = int(stack.size());
	assert(before - after == get<0>(Opcode::getOperation(bytecode)) - get<1>(Opcode::getOperation(bytecode)));
}

//offsetInstrs : CODECOPY指令地址 =》 push CODECOPY指令所需的复制起始偏移量code offset的地址
//sizeInstrs : CODECOPY指令地址 =》 push CODECOPY指令所需的code size的地址
//codecopyBlocks : CODECOPY指令地址 =》指令所在基本块
//需要注意的是并不是所有的CODECOPY指令所需的操作数都是原始的（即不参与运算就能得到的），所以offsetInstrs和sizeInstrs并不包含所有的codecopy指令
void genCODECOPYOffsetAndSizeInstrs(const map<int, EBasicBlock>& blocks, map<int, int>& codecopyBlocks, map<int, int>& offsetInstrs, map<int, int>& sizeInstrs) {
	set<int> codecopyRelatedBlocks;
	for (auto& bb : blocks)
		for (auto& i : bb.second.getInstrs())
			if (i.second == "CODECOPY") {
				codecopyBlocks.insert(make_pair(i.first, bb.first));
				//codecopyInstrs.insert(i.first);
				codecopyRelatedBlocks.insert(bb.first);
			}

	for (auto& bb : codecopyRelatedBlocks) {
		vector<int> stack(1024, 1);
		for (auto& i : blocks.at(bb).getInstrs()) {
			if (i.second == "CODECOPY") {
				int offset = stack[stack.size() - 2];
				int size = stack[stack.size() - 3];
				if (offset < 0)
					offsetInstrs.insert(make_pair(i.first, -offset));
				if (size < 0)
					sizeInstrs.insert(make_pair(i.first, -size));
			}
			instrCODECOPYSim(i.first, i.second, stack);
		}
	}

	//offsetInstrs和sizeInstrs记录都是绝对值，但CODECOPY指令应该至少有一个绝对值
	for (auto& c : codecopyBlocks)
		assert(offsetInstrs.find(c.first) != offsetInstrs.end() || sizeInstrs.find(c.first) != sizeInstrs.end());


}

static map<vector<string>, int>stack2NodeID;
void Contract::traverseBlocks(map<int, ECFGNode>& runtimeNodes, map<int, EBasicBlock>& blocks, int preID, int curBlock, vector<string>& stack, vector<int>& visited, const set<int>& natTgt, const set<int>& jmpiTgt) {
	if (natTgt.find(curBlock) == natTgt.end() && jmpiTgt.find(curBlock) == jmpiTgt.end() && curBlock != 0) {//潜在的 JUMP[in]/[out]块
		visited.push_back(curBlock);
		auto iter1 = visited.rbegin() + 1;
		while (iter1 != visited.rend() && *iter1 != curBlock)
			iter1++;
		if (iter1 != visited.rend()) {
			vector<int> call1(visited.rbegin(), iter1);
			auto iter2 = iter1;
			iter2++;
			while (iter2 != visited.rend() && *iter2 != curBlock)
				iter2++;
			vector<int> call2(iter1, iter2);
			if (call1 == call2) {
				cout << "recursive function call" << endl;
				throw runtime_error("recursive function call");
			}
		}
	}

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

	//displayBlueMsg("after Execution Block " + to_string(bb.getStart()) + " : ");
	//for (auto& i : after) {
	//	if (i[0] == '-') {
	//		int addr = -1;
	//		SSCANF(i.substr(1).c_str(), "%x", &addr);
	//		cout << addr << " ";
	//	}
	//	else
	//		cout << i << " ";
	//}
	//cout << "TOP" << endl;

	string next = blockNext.at(curBlock);
	int target = -1;
	if (next[0] == 's') {
		size_t lastIdx = stoi(next.substr(1));
		SSCANF(stack[stack.size() - 1 - lastIdx].substr(1).c_str(), "%x", &target);
	}
	else
		SSCANF(next.substr(1).c_str(), "%x", &target);
	if (bb.getJumpType() == BlockType::JUMPI) {
		int jumpAddr = target;
		int fallsAddr = bb.getEnd() + 1;
		ECFGNode curNode(&blocks.at(curBlock), jumpAddr, fallsAddr, preID);
		//cout << "New Node : " << curNode.getID() << " " << bb.getStart() << "-" << bb.getEnd() << endl;
		runtimeNodes.insert(pair<int, ECFGNode>(curNode.getID(), curNode));
		blockNodeIDs[curBlock].insert(curNode.getID());

		stack.push_back(to_string(curBlock));
		stack2NodeID.insert(make_pair(stack, curNode.getID()));

		vector<string> key = after; key.push_back(to_string(jumpAddr));

		vector<string> dupStack = after;
		vector<int> dupVisited = visited;
		if (stack2NodeID.find(key) == stack2NodeID.end())
			traverseBlocks(runtimeNodes, blocks, curNode.getID(), jumpAddr, after, visited, natTgt, jmpiTgt);
		else
			runtimeNodes.at(stack2NodeID.at(key)).addParent(curNode.getID());
		key.pop_back(); key.push_back(to_string(fallsAddr));
		if (stack2NodeID.find(key) == stack2NodeID.end())
			traverseBlocks(runtimeNodes, blocks, curNode.getID(), fallsAddr, dupStack, dupVisited, natTgt, jmpiTgt);
		else
			runtimeNodes.at(stack2NodeID.at(key)).addParent(curNode.getID());
	}
	else if (bb.getJumpType() == BlockType::JUMP) {
		int jumpAddr = target;
		ECFGNode curNode(&blocks.at(curBlock), jumpAddr, -1, preID);
		//cout << "New Node : " << curNode.getID() << " " << bb.getStart() << "-" << bb.getEnd() << endl;
		runtimeNodes.insert(pair<int, ECFGNode>(curNode.getID(), curNode));
		blockNodeIDs[curBlock].insert(curNode.getID());

		stack.push_back(to_string(curBlock));
		stack2NodeID.insert(make_pair(stack, curNode.getID()));

		vector<string> key = after; key.push_back(to_string(jumpAddr));
		if (stack2NodeID.find(key) == stack2NodeID.end())
			traverseBlocks(runtimeNodes, blocks, curNode.getID(), jumpAddr, after, visited, natTgt, jmpiTgt);
		else
			runtimeNodes.at(stack2NodeID.at(key)).addParent(curNode.getID());
	}
	else if (bb.getJumpType() == BlockType::CREATE || bb.getJumpType() == BlockType::MESSAGECALL || bb.getJumpType() == BlockType::NATURAL) {
		int fallsAddr = bb.getEnd() + getOpcodeSize(bb.getInstrs().at(bb.getEnd()));
		ECFGNode curNode(&blocks.at(curBlock), -1, fallsAddr, preID);
		//cout << "New Node : " << curNode.getID() << " " << bb.getStart() << "-" << bb.getEnd() << endl;
		runtimeNodes.insert(pair<int, ECFGNode>(curNode.getID(), curNode));
		blockNodeIDs[curBlock].insert(curNode.getID());

		stack.push_back(to_string(curBlock));
		stack2NodeID.insert(make_pair(stack, curNode.getID()));

		vector<string> key = after; key.push_back(to_string(fallsAddr));
		if (stack2NodeID.find(key) == stack2NodeID.end())
			traverseBlocks(runtimeNodes, blocks, curNode.getID(), fallsAddr, after, visited, natTgt, jmpiTgt);
		else
			runtimeNodes.at(stack2NodeID.at(key)).addParent(curNode.getID());
	}
	else if (bb.getJumpType() == BlockType::REVERT || bb.getJumpType() == BlockType::INVALID || bb.getJumpType() == BlockType::RETURN || bb.getJumpType() == BlockType::STOP || bb.getJumpType() == BlockType::SELFDESTRUCT) {
		ECFGNode curNode(&blocks.at(curBlock), -1, -1, preID);
		//cout << "New Node : " << curNode.getID() << " " << bb.getStart() << "-" << bb.getEnd() << endl;
		runtimeNodes.insert(pair<int, ECFGNode>(curNode.getID(), curNode));
		blockNodeIDs[curBlock].insert(curNode.getID());

		stack.push_back(to_string(curBlock));
		stack2NodeID.insert(make_pair(stack, curNode.getID()));
	}

}

extern map<vector<int>, int> jumpInfoIDs;

void dfs(const map<int, ECFGNode>& nodes, vector<int>& ids) {
	vector<int> stack; stack.push_back(0); ids.push_back(0);
	set<int> visited;
	while (!stack.empty()) {
		int top = stack.back();
		bool flag = false;
		int jumpID = nodes.at(top).getJumpID();
		int fallsID = nodes.at(top).getFallsID();
		if (jumpID != -1 && visited.find(jumpID) == visited.end()) {
			stack.push_back(jumpID);
			visited.insert(jumpID);
			ids.push_back(jumpID);
			flag = true;
		}
		else if (fallsID != -1 && visited.find(fallsID) == visited.end()) {
			stack.push_back(fallsID);
			visited.insert(fallsID);
			ids.push_back(fallsID);
			flag = true;
		}

		if (!flag)
			stack.pop_back();
	}
}

CFG* Contract::buildCFG() {
	CFG* cfg = new CFG();
	buildContractCFG(cfg, runtimeNodes);
	return cfg;
}

int Contract::getAddrSize() {
	//get JUMP/JUMPI target size
	//一般而言，第一个基本块为JUMPI，且跳转地址由JUMPI的上一条指令得到
	//目前测试有一用例首基本块不是JUMPI块
	int size = -1;
	for (auto& bb : blocks) {
		const map<int, string>& instrs = bb.second.getInstrs();
		if (instrs.size() >= 2) {
			auto iter = instrs.rbegin();
			string last = iter->second;
			iter++;
			string secLast = iter->second;
			if (last.find("JUMP") != string::npos && secLast.find("PUSH") != string::npos) {
				vector<string> instrParts;
				boost::split(instrParts, secLast, boost::is_any_of(" "));
				return (int)instrParts[1].size() / 2 - 1;
			}
		}
	}

	assert(false);
	return size;
}
void Contract::genJUMPDESTs(set<int>& JUMPDESTs) {
	for (auto& i : instructions)
		if (i.second == "JUMPDEST") {
			JUMPDESTs.insert(i.first);
		}
}

void stackOp1(vector<int>& stack) {//AND OR XOR SUB DIV SHL SHR
	int first = stack.back(); stack.pop_back();
	int second = stack.back(); stack.pop_back();
	assert(first >= 0 || second >= 0);//不能同时均为addr
	stack.push_back(first < second ? first : second);
}
void stackOp2(vector<int>& stack) {//ADD MUL
	int first = stack.back(); stack.pop_back();
	int second = stack.back(); stack.pop_back();
	//assert(first >= 0 || second >= 0);//不能同时均为addr
	assert(!(first < 0 && second < 0) || first == second);
	if (first < 0 && first == second) {
		stack.push_back(first);
	}
	else
		stack.push_back(first < second ? first : second);
}

void stackOp1(vector<string>& stack) {//AND OR XOR SUB DIV SHL SHR
	string first = stack.back(); stack.pop_back();
	string second = stack.back(); stack.pop_back();
	assert(first[0] != '-' || second[0] != '-');//不能同时均为addr
	assert(!(first[0] == '-' && second[0] == 's'));
	assert(!(first[0] == 's' && second[0] == '-'));
	if (first[0] == '-')
		stack.push_back(first);
	else if (second[0] == '-')
		stack.push_back(second);
	else//默认未知地址不会进行算术运算
		stack.push_back("1");
}

void stackOp2(vector<string>& stack) {//ADD MUL
	string first = stack.back(); stack.pop_back();
	string second = stack.back(); stack.pop_back();
	//地址之间的运算只能在确定的值间进行运算，也就是说地址不能跨基本块进行运算
	//0x5370645B7af206e866bB021925Db56f7ad4B286c的9790指令 PUSH2 0x01c0的0x01c0(448)为一JUMPDEST地址，但在9790处push的值不为地址
	//之前我们用assertion来强制规定地址的运算只能在确定的值之间，现在采取折中方案，如果碰到可疑地址(负值)与一不确定数(依赖于一开始的栈中值)进行 ADD MUL操作时的结果统一按1处理
	//assert(!(first[0] == '-' && second[0] == 's'));
	//assert(!(first[0] == 's' && second[0] == '-'));
	if ((first[0] == '-' && second[0] == 's') || (first[0] == 's' && second[0] == '-')) {
		cout << "Binary operation of suspicious address and unknown value" << endl;
		stack.push_back("1");
	}
	else {

		assert(!(first[0] == '-' && second[0] == '-' && first != second));
		if (first[0] == '-')
			stack.push_back(first);
		else if (second[0] == '-')
			stack.push_back(second);
		else//默认未知地址不会进行算术运算
			stack.push_back("1");
	}
}

void pushOpInstr(int pc, int bytecode, string value, int addrSize, vector<int>& stack, const set<int>& JUMPDESTs) {
	if (bytecode - 0x60 + 1 == addrSize) {
		int addr = -1;
		SSCANF(value.c_str(), "%x", &addr);
		//assert(addr != -1);
		if (JUMPDESTs.find(addr) != JUMPDESTs.end()) {
			stack.push_back(-addr);
		}
		else {
			stack.push_back(2);
		}
	}
	else {
		stack.push_back(2);
	}
}
void pushOpTag(int pc, int bytecode, string value, int addrSize, vector<int>& stack, const set<int>& JUMPDESTs) {
	if (bytecode - 0x60 + 1 == addrSize) {
		int addr = -1;
		SSCANF(value.c_str(), "%x", &addr);
		//assert(addr != -1);
		if (JUMPDESTs.find(addr) != JUMPDESTs.end()) {
			stack.push_back(-pc);
		}
		else {
			stack.push_back(2);
		}
	}
	else {
		stack.push_back(2);
	}
}

//一般情况下，地址的长度不可能超过4个字节，所以用int
int Contract::instrSimulate(int pc, string instr, vector<int>& stack, const int& addrSize, const set<int>& JUMPDESTs, function<void(int, int, string, int, vector<int>&, const set<int>&)> pushOp) {
	int pushPC = -1;
	int target = -1;
	vector<string> instrParts;
	//static set<int> wrongPushDest;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string& opcode = instrParts[0];
	int bytecode = Opcode::getOpcode(opcode);
	int before = int(stack.size());
	switch (bytecode) {
	case 0x57: {//JUMPI
		target = -stack.back();
		stack.pop_back(); stack.pop_back();
		break;
	}
	case 0x56: {//JUMP
		target = -stack.back();
		stack.pop_back();
		break;
	}
	case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
	case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
		//PUSHx
		pushOp(pc, bytecode, instrParts[1], addrSize, stack, JUMPDESTs);
		break;
	}
	case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
		//DUPx
		size_t index = atoi(opcode.substr(3).c_str());//index : 1~16
		stack.push_back(stack[stack.size() - index]);
		break;
	}
	case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
		//SWAPx
		size_t index = atoi(opcode.substr(4).c_str());//index : 1~16
		size_t size = stack.size();
		int temp = stack.back();
		stack[size - 1] = stack[size - index - 1];
		stack[size - index - 1] = temp;
		break;
	}
	case 0x16:case 0x17: case 0x18:case 0x03:case 0x04:case 0x1b:case 0x1c: {
		//AND OR XOR SUB DIV SHL SHR
		stackOp1(stack);
		break;
	}
	case 0x01:case 0x02: {
		//ADD MUL
		stackOp2(stack);
		break;
	}
	default: {//other opcodes
		tuple<int, int> op = Opcode::getOperation(bytecode);
		int delta = get<0>(op);//pop stack
		int alpha = get<1>(op);//push stack
		for (int i = 0; i < delta; i++)
			stack.pop_back();
		for (int i = 0; i < alpha; i++)
			stack.push_back(1);
		break;
	}
	}
	int after = int(stack.size());
	assert(before - after == get<0>(Opcode::getOperation(bytecode)) - get<1>(Opcode::getOperation(bytecode)));
	return target;
}

vector<string> Contract::instrSim(int pc, string instr, vector<string>& stack, vector<string>& tagStack, const int& addrSize, const set<int>& JUMPDESTs, int& curDepth, int& minDepth) {
	string target = "-1";
	string tagTgt = "-1";
	vector<string> instrParts;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string& opcode = instrParts[0];
	int bytecode = Opcode::getOpcode(opcode);
	int before = int(stack.size());
	switch (bytecode) {
	case 0x57: {//JUMPI
		target = stack.back(); tagTgt = tagStack.back();
		stack.pop_back(); stack.pop_back();
		tagStack.pop_back(); tagStack.pop_back();
		curDepth -= 2;
		minDepth = minDepth > curDepth ? curDepth : minDepth;
		break;
	}
	case 0x56: {//JUMP
		target = stack.back(); tagTgt = tagStack.back();
		stack.pop_back();
		tagStack.pop_back();
		curDepth--;
		minDepth = minDepth > curDepth ? curDepth : minDepth;
		break;
	}
	case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
	case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
		//PUSHx
		pushInstr(bytecode, instrParts[1], addrSize, stack, JUMPDESTs);
		pushAddr(pc, bytecode, instrParts[1], addrSize, tagStack, JUMPDESTs);
		curDepth++;
		break;
	}
	case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
		//DUPx
		size_t index = atoi(opcode.substr(3).c_str());//index : 1~16
		stack.push_back(stack[stack.size() - index]);
		tagStack.push_back(tagStack[tagStack.size() - index]);

		int depth = curDepth - int(index);
		minDepth = minDepth > depth ? depth : minDepth;
		curDepth++;

		break;
	}
	case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
		//SWAPx
		size_t index = atoi(opcode.substr(4).c_str());//index : 1~16
		size_t size = stack.size();
		string temp = stack.back();
		stack[size - 1] = stack[size - index - 1];
		stack[size - index - 1] = temp;

		temp = tagStack.back();
		tagStack[size - 1] = tagStack[size - index - 1];
		tagStack[size - index - 1] = temp;

		int depth = curDepth - int(index) - 1;
		minDepth = minDepth > depth ? depth : minDepth;
		break;
	}
	case 0x16:case 0x17: case 0x18:case 0x03:case 0x04:case 0x1b:case 0x1c: {
		//AND OR XOR SUB DIV SHL SHR
		stackOp1(stack);
		stackOp1(tagStack);

		curDepth -= 2;//使用栈上的两个操作数
		minDepth = minDepth > curDepth ? curDepth : minDepth;
		curDepth++;
		break;
	}
	case 0x01:case 0x02: {
		//ADD MUL
		stackOp2(stack);
		stackOp2(tagStack);

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
			tagStack.pop_back();
		}
		for (int i = 0; i < alpha; i++) {
			stack.push_back("1");
			tagStack.push_back("1");
		}

		curDepth -= delta;
		minDepth = minDepth > curDepth ? curDepth : minDepth;
		curDepth += alpha;
		break;
	}
	}
	int after = int(stack.size());
	assert(before - after == get<0>(Opcode::getOperation(bytecode)) - get<1>(Opcode::getOperation(bytecode)));
	vector<string> res = { target, tagTgt };
	return res;
}

//遇到inStack中有多个相同的可能地址可能会出错
//action的映射A -> B表示的是inStack中距离栈顶(注意栈顶为vector的尾部)距离为A处的值替换为outStack中距离栈顶为B处的值
void transfer(const vector<int>& inStack, const vector<int>& outStack, map<size_t, size_t>& actions) {
	map<int, set<size_t>> inAddrs;//栈中内容 => 所有可能的索引值
	map<int, set<size_t>> outAddrs;
	for (size_t i = 0; i < inStack.size(); i++)
		if (inStack[i] < 0) {
			inAddrs[inStack[i]].insert(inStack.size() - 1 - i);
		}

	for (size_t i = 0; i < outStack.size(); i++)
		if (outStack[i] < 0) {
			outAddrs[outStack[i]].insert(outStack.size() - 1 - i);
		}

	//测试inStack和outStack中是否有重复的地址（目前假设没有）
	for (auto& i : inAddrs)
		assert(i.second.size() < 2);
	for (auto& i : outAddrs)
		assert(i.second.size() < 2);


	for (auto& i : inAddrs)
		if (outAddrs.find(i.first) != outAddrs.end())
			for (auto& o : outAddrs.at(i.first))
				actions.insert(make_pair(*i.second.begin(), o));
}

int getReturnAddrIdx(const vector<int>& inStack, const vector<int>& outStack) {
	set<int> in;
	set<int> out;
	for (int i = 0; i < inStack.size(); i++)
		if (inStack[i] < 0)
			in.insert(inStack[i]);
	for (int i = 0; i < outStack.size(); i++)
		if (outStack[i] < 0)
			out.insert(outStack[i]);
	vector<int> res;
	set_difference(in.begin(), in.end(), out.begin(), out.end(), back_inserter(res));
	assert(res.size() == 1);

	int i = 0;
	for (auto iter = inStack.rbegin(); iter != inStack.rend(); iter++) {
		if (*iter == res[0])
			break;
		i++;
	}
	return i;
}

bool recursive(const vector<int>& jumpIn) {
	int back = jumpIn.back();
	for (auto riter = jumpIn.rbegin() + 1; riter != jumpIn.rend(); riter++)
		if (*riter == back)
			return true;
	return false;
}

//测试一个基本块会在构建CFG的时候遍历多少次
map<int, int> traverseTimes;

map<vector<int>, int> jumpInfoIDs;

static bool isNewOut = false;
static map<int, int> functions;//函数起始块 => 函数末尾块
static map<int, vector<int>> funcInStacks;//函数起始块 => 未进入函数起始块前的栈中内容
static map<int, vector<int>> funcOutStacks;//函数起始块 => 执行函数末尾块前的栈中内容

static map<int, int> funcOutIdx;//函数起始块 => 执行函数体之前的栈中的对应于函数体跳出地址的索引(从栈顶开始计算)
set<int> funcActs;//所有已经确定函数体部分的函数的起始基本块，替代funcInActs的key值

class funcNode {
public:
	int start;
	int ID = -1;//只有在进行函数相关基本块节点批量生成的时候才会用
	vector<int> curInfo;
	set<vector<int>>pnts;
	int jumpAddr;
	int fallsAddr;

	funcNode(int ID) : ID(ID), start(-1), jumpAddr(-1), fallsAddr(-1) {}
	bool operator<(const funcNode& src) const {
		//要想set中使用自定义类，必须手动实现<函数
		//若!(this < src && src < this)，则src与this相等，此时在set中添加src和this只会有一个元素
		return ID < src.ID;
	}
};

static map<int, int> funcEndNodeID;
static map<int, vector<int>> funcEndStacks;
static map<int, int> outBlocks;
static map<int, set<funcNode>> functionNodes;

void Contract::blockTraversal(map<int, ECFGNode>& runtimeNodes, int preBlock, int currentBlock, vector<int>& stack, const map<int, EBasicBlock>& blocks, set<int>& blockVisited,
	map<int, set<int>>& outEdges, map<int, set<int>>& inEdges,
	const set<int>& natTgt, const set<int>& jmpiTgt, vector<int>& jumps,
	int& addrSize, const set<int>& JUMPDESTs,
	int pntID) {
	//static vector<int> preOutStack;//用以存储遍历过程中进入jump [out]基本块之前的栈
	//static bool isPreOut = false;//用以表示当前节点是否是潜在的jump [out]基本块
	assert(currentBlock == 0 || pntID != -1);

	//cout << "currentBlock : " << currentBlock << endl;
	//size_t beforeSize = blockVisited.size();
	blockVisited.insert(currentBlock);
	//if (blockVisited.size() > beforeSize) {
	//	cout << "new Block : " << currentBlock << " has been visited" << endl;
	//}

	const EBasicBlock& bb = blocks.at(currentBlock);
	const map<int, string>& instrs = bb.getInstrs();
	int end = bb.getEnd();
	int target = -1;

	bool inFunc = false;

	if (natTgt.find(currentBlock) == natTgt.end() && jmpiTgt.find(currentBlock) == jmpiTgt.end() && currentBlock != 0) {
		//能够进入if语句内的JUMP[in/out]的target一定是至少被遍历过两次的基本块
		//if (functions.find(currentBlock) != functions.end() ||
		//	inEdges.at(currentBlock).size() > 1//JUMP [in] target如果是JUMP基本块，则其跳转边只可能为一个基本块(假设错误，jump in target可能是jump out block，此时其跳转边不止一个基本块)
		//	) {
		if (inEdges.at(currentBlock).size() > 1) {
			//仅仅通过入边全是JUMP边无法保证currentBlock为JUMP [in] target
			//存在以下一种情况，以下为solidity代码片段
			/*
			if(a == 1)
				a++;
			else if(a == 2)
				a += 4;
			else if(a == 3)
				a += 10;
			else
				revert();
			return a;
			*/
			//在上述代码片段中在进行"return a"操作的基本块，其入边分别是执行完"a++""a += 4""a += 10"后的JUMP边，该情况满足条件：入边不止一条，且入边均为 JUMP边，但是并不是函数跳转
			bool isJumpInTgt = false;
			for (auto iter = stack.rbegin(); iter != stack.rend(); iter++) {
				if (-(*iter) == blocks.at(preBlock).getEnd() + 1) {
					isJumpInTgt = true;
					break;
				}
			}

			if (isJumpInTgt) {
				//currentBlock is JUMP [in] target, preBlock is JUMP [in] Block
				//currentBlock是函数起始块
				//preBlock 为蓝框，currentBlock为蓝框的后继（绿字）
				jumps.push_back(preBlock);
				if (recursive(jumps)) {
					cout << "recursive function call" << endl;
					throw runtime_error("recursive function call");
				}
				if (funcInStacks.find(currentBlock) == funcInStacks.end())
					funcInStacks.insert(make_pair(currentBlock, stack));

				if (funcActs.find(currentBlock) != funcActs.end() && functions.at(currentBlock) > 0) {//遍历到函数入口第三次及以上，且该函数体是正常结束的
				//if (funcInActs.find(currentBlock) != funcInActs.end()) {//遍历到函数入口第三次及以上
					const vector<int>& inStack = funcInStacks.at(currentBlock);
					const vector<int>& outStack = funcOutStacks.at(currentBlock);
					size_t outSize = stack.size() - inStack.size() + outStack.size();
					vector<int> resStack(outSize, 3);
					size_t returnAddrIdx = funcOutIdx.at(currentBlock);
					for (size_t i = 0; i < stack.size() - returnAddrIdx - 1; i++)
						resStack[i] = stack[i];
					int outTarget = stack[stack.size() - 1 - funcOutIdx.at(currentBlock)];
					assert(outTarget < 0);
					outTarget = -outTarget;

					int funcEndBlock = functions.at(currentBlock);

					inEdges[outTarget].insert(funcEndBlock);
					outEdges[funcEndBlock].insert(outTarget);

					isNewOut = true;
					//displayRedMsg("Found a function");
					set<funcNode>& fNodes = functionNodes.at(currentBlock);
					int jumpOutID = -1;
					for (set<funcNode>::iterator iter = fNodes.begin(); iter != fNodes.end(); iter++) {
						vector<int> curInfo(jumps);
						curInfo.insert(curInfo.end(), iter->curInfo.begin(), iter->curInfo.end());
						int jumpTgt = iter->jumpAddr;
						if (iter->start == funcEndBlock)
							jumpTgt = outTarget;
						ECFGNode node(&blocks.at(iter->start), curInfo, jumpTgt, iter->fallsAddr);
						if (iter->start == funcEndBlock)
							jumpOutID = node.getID();
						runtimeNodes.insert(make_pair(node.getID(), node));
						jumpInfoIDs.insert(make_pair(curInfo, node.getID()));

						funcNode& fNodeRef = const_cast<funcNode&>(*iter);
						fNodeRef.ID = node.getID();
					}
					for (auto& fNode : fNodes) {
						if (fNode.start == currentBlock) {
							runtimeNodes.at(fNode.ID).addParent(pntID);
						}
						else
							for (auto& pnt : fNode.pnts) {
								vector<int> pntInfo(jumps);
								pntInfo.insert(pntInfo.end(), pnt.begin(), pnt.end());
								ECFGNode& curNode = runtimeNodes.at(fNode.ID);
								curNode.addParent(jumpInfoIDs.at(pntInfo));
							}
					}

					jumps.pop_back();
					blockTraversal(runtimeNodes, funcEndBlock, outTarget, resStack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, jumps, addrSize, JUMPDESTs, jumpOutID);
					return;
				}
				else if (funcActs.find(currentBlock) != funcActs.end()) {
					//构造函数体新节点的过程与正常函数一样，只是不再需要进行函数JUMP [out]的下一步遍历
					set<funcNode>& fNodes = functionNodes.at(currentBlock);
					for (set<funcNode>::iterator iter = fNodes.begin(); iter != fNodes.end(); iter++) {
						vector<int> curInfo(jumps);
						curInfo.insert(curInfo.end(), iter->curInfo.begin(), iter->curInfo.end());
						int jumpTgt = iter->jumpAddr;
						ECFGNode node(&blocks.at(iter->start), curInfo, jumpTgt, iter->fallsAddr);
						runtimeNodes.insert(make_pair(node.getID(), node));
						jumpInfoIDs.insert(make_pair(curInfo, node.getID()));

						funcNode& fNodeRef = const_cast<funcNode&>(*iter);
						fNodeRef.ID = node.getID();
					}
					for (auto& fNode : fNodes) {
						if (fNode.start == currentBlock) {
							runtimeNodes.at(fNode.ID).addParent(pntID);
						}
						else
							for (auto& pnt : fNode.pnts) {
								vector<int> pntInfo(jumps);
								pntInfo.insert(pntInfo.end(), pnt.begin(), pnt.end());
								ECFGNode& curNode = runtimeNodes.at(fNode.ID);
								curNode.addParent(jumpInfoIDs.at(pntInfo));
							}
					}

					return;
				}
				else {
					inFunc = true;
				}
			}
		}

		else {
			//确定JUMP[out]target
			bool isOut = outEdges.at(preBlock).size() > 1;
			for (auto& out : outEdges.at(preBlock))
				if (jmpiTgt.find(out) != jmpiTgt.end() || natTgt.find(out) != natTgt.end()) {
					isOut = false;
					break;
				}

			if (isOut) {
				//currentBlock is JUMP [out] target, preBlock is JUMP [out] block
				//preBlock是函数末尾块
				//preBlock为黄框，currentBlock为其后继（绿字）
				if (!isNewOut) {
					//assert(isPreOut); isPreOut = false;
					int jumpIn = jumps.back();

					assert(outEdges.at(jumpIn).size() == 1);//这里认为每个jumpIn block的最终跳转地址是一定的，即调用的一定是一个确定函数（不包含动态调用的情况），不然的话函数体的起始块和末尾块匹配会出错
					int funcIn = *(outEdges.at(jumpIn).begin());
					if (functions.find(funcIn) == functions.end())
						functions[funcIn] = preBlock;
					else
						assert(functions.at(funcIn) == preBlock);//测试是否正确地匹配了函数体的起始块和末尾块
					assert(funcOutStacks.find(funcIn) == funcOutStacks.end());
					funcOutStacks.insert(make_pair(funcIn, stack));
					jumps.pop_back();
					map<size_t, size_t> actions;
					const vector<int>& inStack = funcInStacks.at(funcIn);
					funcOutIdx.insert(make_pair(funcIn, getReturnAddrIdx(inStack, stack)));
					funcActs.insert(funcIn);


					outBlocks[funcIn] = currentBlock;
					assert(funcEndStacks.find(funcIn) == funcEndStacks.end());
					funcEndStacks[funcIn] = stack;
					funcEndNodeID[funcIn] = pntID;
					return;
				}
				isNewOut = false;
			}
		}
	}



	vector<int> info;
	info = jumps; info.push_back(currentBlock);
	auto existIter = jumpInfoIDs.find(info);
	if (existIter != jumpInfoIDs.end()) {
		runtimeNodes.at(existIter->second).addParent(pntID);
		return;
	}

	if (traverseTimes.find(currentBlock) == traverseTimes.end())
		traverseTimes[currentBlock] = 1;
	else
		traverseTimes.at(currentBlock)++;

	for (auto& instr : instrs) {
		//displayBlueMsg("Execute " + to_string(instr.first) + " : " + instr.second);
		//displayStack(stack);
		target = instrSimulate(instr.first, instr.second, stack, addrSize, JUMPDESTs, pushOpInstr);
	}

	int currentID = -1;

	if (bb.getJumpType() == BlockType::JUMPI) {
		int jumpTgt = target;
		int naturalTgt = end + getOpcodeSize(instrs.at(end));
		outEdges[currentBlock].insert(jumpTgt);
		outEdges[currentBlock].insert(naturalTgt);
		inEdges[jumpTgt].insert(currentBlock);
		inEdges[naturalTgt].insert(currentBlock);

		//cout << "-----------------------------" << endl;
		ECFGNode node(&blocks.at(currentBlock), info, jumpTgt, naturalTgt, pntID);
		currentID = node.getID();
		runtimeNodes.insert(pair<int, ECFGNode>(node.getID(), node));
		jumpInfoIDs.insert(make_pair(info, node.getID()));

		vector<int> jmpStack = stack;
		vector<int> jmpJumps = jumps;
		blockTraversal(runtimeNodes, currentBlock, jumpTgt, jmpStack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, jmpJumps, addrSize, JUMPDESTs, node.getID());

		//cout << "$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
		vector<int> natStack = stack;
		vector<int> natJumps = jumps;
		blockTraversal(runtimeNodes, currentBlock, naturalTgt, natStack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, natJumps, addrSize, JUMPDESTs, node.getID());
		//cout << "##########################" << endl;
	}
	else if (bb.getJumpType() == BlockType::JUMP) {
		outEdges[currentBlock].insert(target);
		inEdges[target].insert(currentBlock);

		ECFGNode node(&blocks.at(currentBlock), info, target, -1, pntID);
		currentID = node.getID();
		runtimeNodes.insert(pair<int, ECFGNode>(node.getID(), node));
		jumpInfoIDs.insert(make_pair(info, node.getID()));

		blockTraversal(runtimeNodes, currentBlock, target, stack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, jumps, addrSize, JUMPDESTs, node.getID());
	}
	else if (blocks.at(currentBlock).getJumpType() == BlockType::CREATE || blocks.at(currentBlock).getJumpType() == BlockType::MESSAGECALL ||
		blocks.at(currentBlock).getJumpType() == BlockType::NATURAL) {
		int naturalTarget = end + getOpcodeSize(instrs.at(end));
		outEdges[currentBlock].insert(naturalTarget);
		inEdges[naturalTarget].insert(currentBlock);

		ECFGNode node(&blocks.at(currentBlock), info, -1, naturalTarget, pntID);
		currentID = node.getID();
		runtimeNodes.insert(pair<int, ECFGNode>(node.getID(), node));
		jumpInfoIDs.insert(make_pair(info, node.getID()));

		blockTraversal(runtimeNodes, currentBlock, naturalTarget, stack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, jumps, addrSize, JUMPDESTs, node.getID());
	}
	else if (blocks.at(currentBlock).getJumpType() == BlockType::REVERT || blocks.at(currentBlock).getJumpType() == BlockType::INVALID ||
		blocks.at(currentBlock).getJumpType() == BlockType::RETURN || blocks.at(currentBlock).getJumpType() == BlockType::STOP ||
		blocks.at(currentBlock).getJumpType() == BlockType::SELFDESTRUCT) {
		ECFGNode node(&blocks.at(currentBlock), info, -1, -1, pntID);
		currentID = node.getID();
		runtimeNodes.insert(pair<int, ECFGNode>(node.getID(), node));
		jumpInfoIDs.insert(make_pair(info, node.getID()));
	}

	if (inFunc) {
		info.pop_back();//back为currentBlock
		set<int> visited;
		int endBlock = -1;
		for (int i = currentID; i < ECFGNode::getCount(); i++) {
			visited.insert(i);
		}
		int tempID = -1;
		int outBlock = -1;

		if (outBlocks.find(currentBlock) != outBlocks.end())//由于函数体末尾为revert、assert等语句导致函数无法正常返回，此时无JUMP out block
			outBlock = outBlocks.at(currentBlock);
		for (auto id : visited) {
			const ECFGNode& node = runtimeNodes.at(id);
			const vector<int>& jInfo = node.getJumpInfo();
			funcNode fNode(tempID);
			tempID--;

			if (jInfo.size() == info.size() + 1) {
				if (node.getStart() > endBlock)
					endBlock = node.getStart();
			}

			fNode.start = node.getStart();
			for (size_t i = info.size(); i < jInfo.size(); i++)
				fNode.curInfo.push_back(jInfo[i]);
			fNode.fallsAddr = node.getFallsAddr();
			if (outBlock != -1 && id == funcEndNodeID.at(currentBlock))
				fNode.jumpAddr = outBlock;
			else
				fNode.jumpAddr = node.getJumpAddr();

			if (id != currentID)
				for (auto& pnt : node.getParents()) {
					const vector<int>& pntInfo = runtimeNodes.at(pnt).getJumpInfo();
					vector<int> _pntInfo;
					for (size_t i = info.size(); i < pntInfo.size(); i++)
						_pntInfo.push_back(pntInfo[i]);

					fNode.pnts.insert(_pntInfo);
				}

			functionNodes[currentBlock].insert(fNode);
		}

		if (outBlock == -1) {
			functions.insert(make_pair(currentBlock, -endBlock));//endBlock取负值表明该函数体不是以JUMP [out]结尾的（可能以REVERT、INVALID、SELFDESTRUCT等结尾）
			funcActs.insert(currentBlock);
			return;
		}
		isNewOut = true;
		vector<int> jumps = info; jumps.pop_back();
		vector<int> stack = funcEndStacks.at(currentBlock);

		//displayStack(funcInStacks.at(currentBlock));
		//displayStack(funcOutStacks.at(currentBlock));
		//cout << "------------------------" << endl;
		//displayStack(tempStack);
		//displayStack(stack);

		funcEndStacks.erase(currentBlock);
		assert(runtimeNodes.at(funcEndNodeID.at(currentBlock)).getStart() == functions.at(currentBlock));
		assert(blocks.at(preBlock).getEnd() + 1 == outBlock);
		blockTraversal(runtimeNodes, functions.at(currentBlock), outBlock, stack, blocks, blockVisited, outEdges, inEdges, natTgt, jmpiTgt, jumps, addrSize, JUMPDESTs, funcEndNodeID.at(currentBlock));
	}
}

//const map<int, int>& functions, const map<int, vector<int>>& funcInStacks, const map<int, vector<int>>& funcOutStacks, const map<int, int> funcOutIdx
void Contract::genPushTags(int ID, vector<int>& stack, const int& addrSize, const set<int>& JUMPDESTs, set<int>& pushTags, map<int, int>& push2JumpMap, set<int>& blockVisited) {
	const ECFGNode& node = runtimeNodes.at(ID);
	const map<int, string>& instrs = node.getInstrs();

	int pushPC = -1;
	for (auto& instr : instrs)
		pushPC = instrSimulate(instr.first, instr.second, stack, addrSize, JUMPDESTs, pushOpTag);
	blockVisited.insert(node.getStart());
	if (pushPC != -1) {
		pushTags.insert(pushPC);

		assert(push2JumpMap.find(pushPC) == push2JumpMap.end());
		push2JumpMap.insert(make_pair(pushPC, node.getEnd()));
	}

	int fallsID = node.getFallsID();
	int jumpID = node.getJumpID();
	int fallsAddr = node.getFallsAddr();
	int jumpAddr = node.getJumpAddr();

	vector<int> dupStack = stack;
	if (fallsAddr != -1 && blockVisited.find(fallsAddr) == blockVisited.end()) {
		genPushTags(fallsID, stack, addrSize, JUMPDESTs, pushTags, push2JumpMap, blockVisited);
	}
	if (jumpAddr != -1) {
		if (blockVisited.find(jumpAddr) == blockVisited.end())
			genPushTags(jumpID, dupStack, addrSize, JUMPDESTs, pushTags, push2JumpMap, blockVisited);
		else if (node.getBlockType() == BlockType::JUMP && functions.find(jumpAddr) != functions.end() && functions.at(jumpAddr) > 0) {
			//只有正常的函数体需要JUMP [out]后继续遍历
			//未正常结束的函数体只需要遍历一次
			const vector<int>& inStack = funcInStacks.at(jumpAddr);
			const vector<int>& outStack = funcOutStacks.at(jumpAddr);
			size_t outSize = dupStack.size() - inStack.size() + outStack.size();
			vector<int> resStack(outSize, 3);
			size_t returnAddrIdx = funcOutIdx.at(jumpAddr);
			for (size_t i = 0; i < stack.size() - returnAddrIdx - 1; i++)
				resStack[i] = stack[i];
			int PC = stack[stack.size() - 1 - funcOutIdx.at(jumpAddr)];
			assert(PC < 0);
			pushTags.insert(-PC);
			assert(push2JumpMap.find(-PC) == push2JumpMap.end());
			push2JumpMap.insert(make_pair(-PC, blocks.at(functions.at(jumpAddr)).getEnd()));

			vector<int> nextIDJumpInfo = node.getJumpInfo();
			nextIDJumpInfo.pop_back();

			int jumpOutTgt = node.getEnd() + 1;//一般JUMP [in]紧跟着对应的JUMP [out] target
			nextIDJumpInfo.push_back(jumpOutTgt);
			assert(blockVisited.find(jumpOutTgt) == blockVisited.end());
			genPushTags(jumpInfoIDMaps.at(nextIDJumpInfo), resStack, addrSize, JUMPDESTs, pushTags, push2JumpMap, blockVisited);
			//if (blockVisited.find(jumpOutTgt) == blockVisited.end()) {
			//	genPushTags(jumpInfoIDMaps.at(nextIDJumpInfo), resStack, addrSize, JUMPDESTs, pushTags, push2JumpMap, blockVisited);
			//}
		}
	}
}

void Contract::getJumpITgt(const map<int, EBasicBlock>& blocks, set<int>& jmpTgt) {
	for (auto& bb : blocks)
		//Here assume JUMPI's jump target is pushed into the stack by the previous instruction
		if (bb.second.getJumpType() == BlockType::JUMPI) {
			map<int, string>::const_reverse_iterator riter = bb.second.getInstrs().rbegin();
			riter++;
			int pushPc = riter->first;
			string instr = riter->second;
			//仅通过字节码序列构建时由于未去除掉末尾冗余指令(metahash相关),所以末尾冗余指令可能会出现JUMPI指令的上一条指令不为PUSH指令的现象
			if (instr.find("PUSH") != string::npos) {
				vector<string> instrParts;
				boost::split(instrParts, instr, boost::is_any_of(" "));
				int tgt = boost::multiprecision::uint256_t(instrParts[1]).convert_to<int>();
				jmpTgt.insert(tgt);
			}
		}
}
void Contract::getNaturalTgt(const map<int, EBasicBlock>& blocks, set<int>& natTgt) {
	for (auto& bb : blocks)
		if (bb.second.getJumpType() == BlockType::JUMPI ||
			bb.second.getJumpType() == BlockType::CREATE || bb.second.getJumpType() == BlockType::MESSAGECALL ||
			bb.second.getJumpType() == BlockType::NATURAL) {
			int end = bb.second.getEnd();
			int tgt = end + getOpcodeSize(bb.second.getInstrs().at(end));
			natTgt.insert(tgt);
		}
}

void generateBlockDotGraph(string fileName, const map<int, set<int>>& outEdges) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : outEdges) {
		string blockName = "Block_" + to_string(n.first);
		string label = "Block_" + to_string(n.first);
		dotFile += blockName + "[label = \"" + label + "\"]\r\n";
		for (auto& c : n.second) {
			dotFile += "\tBlock_" + to_string(n.first) + " -> " + "Block_" + to_string(c) + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}

bool blockInvalid(const EBasicBlock& bb) {
	for (auto& i : bb.getInstrs())
		if (i.second.find("Missing Opcode") != string::npos)
			return false;
	return true;
}

void Contract::genBytecodeCFG(map<int, ECFGNode>& runtimeNodes, map<int, EBasicBlock>& blocks, map<int, string>& instrs) {
	stack2NodeID.clear();
	int addrSize = getAddrSize();
	set<int> JUMPDESTs; genJUMPDESTs(JUMPDESTs);
	for (auto& bb : blocks)
		if (blockInvalid(bb.second))
			genStackChanges(bb.second, addrSize, JUMPDESTs);
	ECFGNode::resetCount();
	vector<string>stack;
	vector<int> visited;
	set<int> jmpiTgt; getJumpITgt(blocks, jmpiTgt);
	set<int> natTgt; getNaturalTgt(blocks, natTgt);
	try {
		traverseBlocks(runtimeNodes, blocks, -1, 0, stack, visited, natTgt, jmpiTgt);
		//最终生成的CFGNode总数比通过srcmap生成的Node数多1
		//这是因为下述两种情况进入到 revert基本块的栈深度差1，因此revert基本块多生成了一个节点
		//1.calldata不满四个字节
		//2.calldata前四个字节不匹配任意函数

		//由于solc自身优化的存在，会将一些相同的基本块合并，导致很多函数JUMP [out]跳转地址相同，从而导致不同地址JUMP [in]到函数体的起始节点是同一节点（因为JUMP [out]地址相同）
		//这就减少了函数体相关节点的构造

		//for (auto& b : blocks)
		//	if (blockNodeIDs.find(b.first) == blockNodeIDs.end())
		//		cout << "Block " << b.first << " not visited" << endl;

		//generateBlockDotGraph("C:\\Users\\ASUS\\Desktop\\temp\\block.dot", outEdges);


		//删除由metahash导致的字节码序列末尾多余的基本块和由于revert等指令导致的函数末尾未被遍历的基本块
		int maxEnd = 0;
		for (map<int, EBasicBlock>::iterator citer = blocks.begin(); citer != blocks.end();)
			if (blockNodeIDs.find(citer->first) == blockNodeIDs.end()) {
				for (auto& i : citer->second.getInstrs())
					instrs.erase(i.first);
				citer = blocks.erase(citer);
			}
			else {
				maxEnd = blocks.at(citer->first).getEnd() > maxEnd ? blocks.at(citer->first).getEnd() : maxEnd;
				citer++;
			}

		//指令末尾有部分指令未形成基本块，也需去除
		auto delIter = instrs.find(maxEnd); delIter++;
		while (delIter != instrs.end()) {
			delIter = instrs.erase(delIter);
		}
	}
	catch (runtime_error err) {
		this->isRecursive = true;
		return;
	}
}

void Contract::genFuncInTgt(const map<int, ECFGNode>& nodes, const map<int, EBasicBlock>& blocks, set<int>& potentialTgt) {
	set<int> excludedTgt;
	getJumpITgt(blocks, excludedTgt);
	getNaturalTgt(blocks, excludedTgt);
	excludedTgt.insert(0);//起始基本块不可能为函数体开头

	//这里判断是否是potentialTgt的前提是判断同一block形成的不同CFGNode的父节点是否相同（这里的相同指的是父节点的个数以及出现的基本块的个数）

	for (auto& i : blockNodeIDs) {
		if (excludedTgt.find(i.first) != excludedTgt.end())
			continue;
		//需要首先判断每个基本块的父节点基本块形成的节点数量都需要小于该节点
		set<int> allPntAddrs;
		for (auto& id : i.second)
			for (auto p : nodes.at(id).getParents())
				allPntAddrs.insert(nodes.at(p).getStart());
		bool less = true;
		for (auto& pa : allPntAddrs)
			if (blockNodeIDs.at(pa).size() >= i.second.size()) {
				less = false;
				break;
			}
		if (!less)
			continue;

		//下面判断的是同一个基本块生成的不同节点的父节点的基本块信息是否相同
		map<int, int> pntAddrNums;

		auto begin = i.second.begin();
		for (auto& pnt : nodes.at(*begin).getParents())
			pntAddrNums[nodes.at(pnt).getStart()]++;
		begin++;
		for (auto iter = begin; iter != i.second.end(); iter++) {
			map<int, int> addrNums;
			for (auto& pnt : nodes.at(*iter).getParents())
				addrNums[nodes.at(pnt).getStart()]++;

			if (addrNums.size() == pntAddrNums.size()) {
				bool isSame = true;
				for (auto& a : addrNums)
					if (pntAddrNums.find(a.first) == pntAddrNums.end() || pntAddrNums.at(a.first) != a.second) {
						isSame = false;
						break;
					}
				if (!isSame) {
					potentialTgt.insert(i.first);
					break;
				}
			}
			else {
				potentialTgt.insert(i.first);
				break;
			}
		}
	}


}

void Contract::genFuncbodyBlocks(const map<int, ECFGNode>& nodes, int funcStart, int funcStartID, map<int, map<int, tuple<int, int>>>& IDAddrs, map<int, map<int, int>>& funcEnds, map<int, map<int, vector<int>>>& funcTopLevelIDs, set<int>& potentialTgt, int depth, map<int, vector<int>>& left, map<int, vector<int>>& funcIDs) {
	//IDAddrs 是为了保存CFG中所有完整的函数子图的所有节点
	//IDAddrs 函数起始块 => 该函数体在CFG中的子图所有NodeID => (Node起始地址，Node在该函数体中的函数调用深度)
	//不直接保存地址的原因是因为可能在函数中同一个基本块可能出现两次
	//funcEnds是保存所有即将跳出函数体的函数体末尾基本块（节点ID=>基本块起始地址），一个函数可能有多个JUMP [out]基本块
	//funcEnds 函数起始块 => JUMP [out] Node ID=> Node所在block的起始地址
	//! 注意：funcEnds仅包含节点后继不同的 Node ID,因此funcEnds不包括REVERT块、INVALID块等
	//! 因此，如果出现非正常终止的函数体时，其funcEnds为空

	//string space = "";
	//for (int i = 0; i < depth; i++)
	//	space += " ";

	//displayBlueMsg(space + "funcStart : " + to_string(funcStart) + ", funcStartID : " + to_string(funcStartID));

	vector<queue<int>> levelOrders;
	vector<int> funcStartIDs;
	queue<int> q;
	q.push(funcStartID);
	levelOrders.push_back(q);

	funcStartIDs.push_back(funcStartID);
	for (auto& i : blockNodeIDs.at(funcStart))
		if (i != funcStartID) {
			queue<int> que;
			que.push(i);
			levelOrders.push_back(que);

			funcStartIDs.push_back(i);
		}

	set<int> IDVisited;
	IDVisited.insert(funcStartID);

	while (!levelOrders[0].empty()) {
		vector<int> fronts;
		for (auto& i : levelOrders) {
			fronts.push_back(i.front());
			i.pop();
		}

		size_t beforeInQueSize = levelOrders[0].size();//还在队列中待处理的节点

		int front_0 = fronts[0];
		for (auto& i : fronts)
			assert(nodes.at(i).getStart() == nodes.at(front_0).getStart());

		//cout << space;
		//for (size_t i = 0; i < fronts.size(); i++)
		//	cout << fronts[i] << " ";
		//cout << endl;
		//cout << "----------------------------" << endl;

		int jumpAddr = nodes.at(fronts[0]).getJumpAddr();
		int fallsAddr = nodes.at(fronts[0]).getFallsAddr();
		bool same = true;
		for (size_t i = 1; i < fronts.size(); i++) {
			int jmp = nodes.at(fronts[i]).getJumpAddr();
			int fall = nodes.at(fronts[i]).getFallsAddr();
			if (!(jumpAddr == jmp && fallsAddr == fall)) {
				same = false;
				//JUMPI block不可能作为函数体的结尾
				assert(fall == -1);
				break;
			}
		}
		//same判断的是当前节点基本块对应的所有节点是否后继地址（JUMP和NATURAL）完全相同
		//相同表明其后继是可以被纳入到该函数体的，所以需要将其后继加入到队列中
		//不相同表明仅其本身可以被纳入到函数体，其后继不能加入函数体
		if (same) {
			int curBlock = nodes.at(fronts[0]).getStart();
			if (potentialTgt.find(curBlock) != potentialTgt.end() && curBlock != funcStart) {
				if (IDAddrs.find(curBlock) != IDAddrs.end()) {
					IDAddrs.at(curBlock).clear();
					funcEnds.at(curBlock).clear();
				}
				map<int, vector<int>> subLeft;
				map<int, vector<int>> subFuncIDs;
				//left 一维个数表明CFG中有多少个函数体
				//left 二维个数表明函数体有多少个终止基本块
				//生成新函数体的默认depth为0，但为了并入到新函数体中需要重新
				genFuncbodyBlocks(nodes, curBlock, fronts[0], IDAddrs, funcEnds, funcTopLevelIDs, potentialTgt, depth + 1, subLeft, subFuncIDs);
				for (auto& subGraph : IDAddrs.at(curBlock)) {
					IDAddrs[funcStart][subGraph.first] = make_tuple(get<0>(subGraph.second), get<1>(subGraph.second) + 1);
				}
				//需要将遍历到的所有子图函数体节点都加入到IDAddrs
				//注意是从fronts中的函数开始节点遍历到的函数体节点加入到IDVisited中，而不是所有函数体起始基本块形成的节点的CFG
				for (size_t i = 0; i < fronts.size(); i++)
					for (auto& id : subFuncIDs.at(fronts[i]))
						IDVisited.insert(id);

				//由于可能出现非正常终止的函数体，此时left为空
				if (!subLeft.empty()) {
					size_t endNodeNum = subLeft.begin()->second.size();
					vector<bool> isSame(endNodeNum, true);
					for (size_t i = 0; i < endNodeNum; i++) {//有多少个终止节点
						int jumpAddr = nodes.at(subLeft.at(fronts[0])[i]).getJumpAddr();
						int fallsAddr = nodes.at(subLeft.at(fronts[0])[i]).getFallsAddr();

						bool same = true;
						for (size_t j = 1; j < fronts.size(); j++) {//有多少个函数体子图
							int jmp = nodes.at(subLeft.at(fronts[j])[i]).getJumpAddr();
							int fall = nodes.at(subLeft.at(fronts[j])[i]).getFallsAddr();
							if (!(jumpAddr == jmp && fallsAddr == fall)) {
								same = false;
								//JUMPI block不可能作为函数体的结尾
								assert(fall == -1);
								break;
							}
						}
						isSame[i] = same;
					}

					for (size_t i = 0; i < isSame.size(); i++)
						if (isSame[i])
							for (size_t j = 0; j < fronts.size(); j++) {
								int jmpID = nodes.at(subLeft.at(fronts[j])[i]).getJumpID();
								int fallsID = nodes.at(subLeft.at(fronts[j])[i]).getFallsID();
								if (jmpID != -1 && IDVisited.find(jmpID) == IDVisited.end()) {
									levelOrders[j].push(jmpID);
									IDVisited.insert(jmpID);
								}
								if (fallsID != -1 && IDVisited.find(fallsID) == IDVisited.end()) {
									levelOrders[j].push(fallsID);
									IDVisited.insert(fallsID);
								}
							}
						else {//子图函数体的边界也为自身函数体的边界
							int leftID = subLeft.at(fronts[0])[i];
							funcEnds[funcStart][leftID] = nodes.at(leftID).getStart();

							//还需要将边界上传到上一层left
							for (size_t j = 0; j < fronts.size(); j++)
								left[funcStartIDs[j]].push_back(subLeft.at(fronts[j])[i]);
						}
				}
			}
			else {
				for (size_t i = 0; i < levelOrders.size(); i++)
					funcIDs[funcStartIDs[i]].push_back(fronts[i]);

				for (auto& n : fronts)
					IDAddrs[funcStart][fronts[0]] = make_tuple(nodes.at(fronts[0]).getStart(), 0);
				for (size_t i = 0; i < fronts.size(); i++) {
					int jmpID = nodes.at(fronts[i]).getJumpID();
					int fallsID = nodes.at(fronts[i]).getFallsID();
					if (jmpID != -1 && IDVisited.find(jmpID) == IDVisited.end()) {
						levelOrders[i].push(jmpID);
						IDVisited.insert(jmpID);
					}
					if (fallsID != -1 && IDVisited.find(fallsID) == IDVisited.end()) {
						levelOrders[i].push(fallsID);
						IDVisited.insert(fallsID);
					}
				}
			}
		}
		else {//如果发现节点的后继地址不相同的话，则只可能是JUMP的地址不同
			for (size_t i = 0; i < levelOrders.size(); i++)
				funcIDs[funcStartIDs[i]].push_back(fronts[i]);

			IDAddrs[funcStart][fronts[0]] = make_tuple(nodes.at(fronts[0]).getStart(), 0);
			for (size_t i = 0; i < fronts.size(); i++) {
				left[funcStartIDs[i]].push_back(fronts[i]);
			}
			funcEnds[funcStart][fronts[0]] = nodes.at(fronts[0]).getStart();
		}

		size_t afterInQueSize = levelOrders[0].size();
		vector<queue<int>> test = levelOrders;
		for (size_t i = 0; i < beforeInQueSize; i++)
			for (auto& q : test)
				q.pop();

		size_t queSize = test[0].size();
		for (auto& q : test)
			assert(q.size() == queSize);

		//vector<queue<int>> outTest = test;
		//displayBlueMsg("Newly entered Node");
		//displayPurpleMsg("******************");
		//for (auto& que : outTest) {
		//	while (!que.empty()) {
		//		int top = que.front();
		//		cout << top << " ";
		//		que.pop();
		//	}
		//	cout << endl;
		//}
		//displayPurpleMsg("******************");

		for (size_t i = 0; i < afterInQueSize - beforeInQueSize; i++) {
			vector<int> testFronts;
			for (auto& q : test) {
				testFronts.push_back(q.front());
				q.pop();
			}

			int _0 = testFronts[0];
			for (auto& i : testFronts)
				assert(nodes.at(i).getStart() == nodes.at(_0).getStart());

		}

	}


	//非正常终止的函数体funcEnds应为空
	if (funcEnds.find(funcStart) == funcEnds.end())
		funcEnds[funcStart] = { };

	if (funcTopLevelIDs.find(funcStart) == funcTopLevelIDs.end())
		funcTopLevelIDs[funcStart] = funcIDs;
}

void Contract::genSrcMapFile(const map<int, vector<string>>& instrMaps, map<int, string>& instrs, string fileName) {
	ofstream outfile(fileName);
	if (!outfile) {
		cerr << "Fail to open " << fileName << endl;
		exit(-1);
	}
	for (auto& i : instrMaps) {
		outfile << i.first << " " << instrs.at(i.first) << endl;
		outfile << getSrcMap(i.second) << endl;
		//cout << getSrcMap(i.second) << endl;
		outfile << endl;
	}
	outfile.close();
}

void generateDot(string fileName, const map<int, ECFGNode>& nodes) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : nodes) {
		string blockName = "Node_" + to_string(n.first);
		string label = "Node_" + to_string(n.first) + "#" + to_string(n.second.getStart()) + "-" + to_string(n.second.getEnd());
		//label += "#" + n.second.getJumpIn();
		//label = "";
		string color = "";
		if (n.second.getBlockType() == BlockType::INVALID)
			color = ", color = red";

		string nodeLabel = "[label = \"" + label + "\"" + color + "]";
		//string nodeLabel = "";
		dotFile += blockName + nodeLabel + "\r\n";
		for (auto p : n.second.getParents()) {
			if (p == -1)
				continue;
			string parentName = "Node_" + to_string(p);
			dotFile += "\t" + parentName + " -> " + blockName + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}
void generateTransform(string fileName, const map<int, ECFGNode>& nodes) {
	ofstream outFile(fileName);
	string transformFile;
	for (auto& n : nodes)
		transformFile += "Node_" + to_string(n.first) + "\t" + to_string(n.second.getStart()) + "-" + to_string(n.second.getEnd()) + "\n";
	for (auto& n : nodes)
		for (auto& pnt : n.second.getParents()) {
			if (pnt == -1)
				continue;
			string srcNo = to_string(pnt);
			string dstNo = to_string(n.first);
			transformFile += "#\tNode_" + srcNo + "\t" + "Node_" + dstNo + "\n";
		}
	outFile << transformFile;
	outFile.close();
}

void Contract::genRuntimeByteCFG() {
	genInstrs(runtime, instructions);
	string name = this->name;
	name[name.find_last_of(':')] = '.';
	generateDisasm(instructions, name + ".runtime");

	map<int, vector<string>> instrMaps;
	if (!srcmapRuntime.empty()) {//没有进行源代码编译的情况下srcmapRuntime为空
		genInstrSrcmap(srcmapRuntime, instructions, instrMaps);
		genSrcMapFile(instrMaps, instructions, name + ".srcmap");//这里去除了instructions末尾多余的指令
	}

	genBasicBlocks(instructions, blocks);

	genBytecodeCFG(runtimeNodes, blocks, instructions);
	genCFGEdges(runtimeNodes);
	//if(!instrMaps.empty())
	//	generateDotGraph(runtimeNodes, name + ".dot", instrMaps);
	//generateDisasm(instructions, name + ".necessary.runtime");
	if (isRecursive)
		return;
	generateDot(name + ".dot", runtimeNodes);
	//generateDot(name + ".dot", runtimeNodes);
	//generateTransform(name + ".transform", runtimeNodes);
}

void Contract::generateTagInstrsFile(string fileName, const set<int>& pushTags) {
	map<int, int> JUMPDESTAddrs2tagNum;
	map<int, int> pushTags2TagNum;
	int tagNum = 0;
	for (auto& i : pushTags) {
		string opcode = instructions.at(i);
		vector<string> temp;
		boost::split(temp, opcode, boost::is_any_of(" "));
		int addr = -1;
		SSCANF(temp[1].c_str(), "%x", &addr);
		if (JUMPDESTAddrs2tagNum.find(addr) == JUMPDESTAddrs2tagNum.end()) {
			JUMPDESTAddrs2tagNum.insert(make_pair(addr, tagNum));
			tagNum++;
		}
		pushTags2TagNum.insert(make_pair(i, JUMPDESTAddrs2tagNum.at(addr)));
	}

	ofstream outFile(fileName);
	for (auto& instr : instructions) {
		string opcode;
		if (instr.second == "JUMPDEST")
			opcode = "tag " + to_string(JUMPDESTAddrs2tagNum.at(instr.first));
		else if (pushTags.find(instr.first) != pushTags.end()) {
			opcode = "push tag " + to_string(pushTags2TagNum.at(instr.first));
		}
		else
			opcode = instr.second;

		outFile << instr.first << " " << opcode << endl;
	}

	outFile.close();
}

void Contract::assertAnalysis() {
	string name = this->name;
	name[name.find_last_of(':')] = '.';
	//replace(name.begin(), name.end(), ':', '.');
	//generateDisasm(instructions, name + ".runtime");
	//genSrcMapFile(srcmapRuntime, instructions, name + ".srcmap");

	map<int, set<int>> edges;
	pruningInvalids(runtimeNodes, edges);
	//generateInvalidDotGraph(runtimeNodes, name + ".dot", edges);
	if (edges.empty()) {
		cout << "NoInvalid" << endl;
		//cout << "no INVALID instructions found" << endl;
		return;
	}

	//jmpiTgt和natTgt均是block 开始地址，不是Node ID
	set<int> jmpiTgt; getJumpITgt(blocks, jmpiTgt);
	set<int> natTgt; getNaturalTgt(blocks, natTgt);

	//map<int, set<int>> scc;
	//testSCC(edges, scc, jmpiTgt, natTgt, runtimeNodes);

	vector<int> redundantInvs;//所有冗余的INVALID Node ID
	//isRedundant(edges, runtimeNodes, jmpiTgt, natTgt, redundantInvs, name);
	set<int> loopInvalids;

	parallelSolve(edges, runtimeNodes, jmpiTgt, natTgt, loopInvalids, redundantInvs);

	//0x3528C164e3fCA20E2333Cf58Ab4B1c99DeF83347
	//string debugNodeIDStr = "30 126 136 174 193 198 202 207 302 307 343 348 771 781 819 838 843 847 852 1471 1476 1913 1923 1961 1980 1985 1989 1994 2089 2094 2130 2135 2860 2881 2886 3263 3268";
	//0xc09315c63f477ba1e15120d2b3a43f109eea9787
	//string debugNodeIDStr = "104 106 167 168 211 310 418 420";
	//vector<string> debugIDs;
	//boost::split(debugIDs, debugNodeIDStr, boost::is_any_of(" "));
	//for (auto& s : debugIDs)
	//	redundantInvs.push_back(atoi(s.c_str()));
	//for (auto& r : redundantInvs)
	//	cout << r << " ";
	//cout << endl;

	cout << "Constraint solving ends" << endl;
	set<int> invIDs;
	set<int> invAddrs;
	map<int, set<int>> invAddr2IDs;
	for (auto& i : redundantInvs) {
		invAddrs.insert(runtimeNodes.at(i).getStart());
		invIDs.insert(i);
		invAddr2IDs[runtimeNodes.at(i).getStart()].insert(i);
	}


	map<int, int> invRelatedInstrStart =
		getInvRelatedInstrsStart(invAddrs, edges, runtimeNodes, jmpiTgt, natTgt);
	//对于未计算出冗余相关指令序列的INVALID进行除名
	for (auto iter = invAddrs.begin(); iter != invAddrs.end();) {
		if (invRelatedInstrStart.find(*iter) == invRelatedInstrStart.end()) {
			int invAddr = *iter;
			iter = invAddrs.erase(iter);
			for (auto& id : invAddr2IDs.at(invAddr))
				invIDs.erase(id);
			invAddr2IDs.at(invAddr).clear();
		}
		else
			iter++;
	}

	bool redundancy = false;
	for (auto& inv : invAddr2IDs)
		if (!inv.second.empty()) {
			redundancy = true;
			break;
		}
	if (!redundancy) {
		cout << "NoRedundantInvalid" << endl;
		return;
	}

	auto invBegin = invIDs.begin();
	cout << *invBegin;
	invBegin++;
	while (invBegin != invIDs.end()) {
		cout << "," << *invBegin;
		invBegin++;
	}
	cout << endl;

	set<int> allInvalidAddrs;
	set<int> allNonLoopInvalidAddrs;
	set<int> affectedInvalidAddrs;
	for (auto& i : invIDs)
		affectedInvalidAddrs.insert(runtimeNodes.at(i).getStart());
	for (auto& i : runtimeNodes)
		if (i.second.getBlockType() == BlockType::INVALID) {
			allInvalidAddrs.insert(i.second.getStart());
			if (loopInvalids.find(i.first) == loopInvalids.end())
				allNonLoopInvalidAddrs.insert(i.second.getStart());
		}
	cout << "Affected Assertion " << affectedInvalidAddrs.size() << " " << allNonLoopInvalidAddrs.size() << " " << allInvalidAddrs.size() << endl;

	map<int, int> invTypes;
	//type == 1 表明为正常INVALID
	//type == 2 表明不能删除JUMPDEST
	//在判断inv type == 2时需要判断JUMP地址是否在type == 1的冗余序列中
	//示例由2513、3235和4052三个invalid地址的上一个push 的地址为2514，这时虽然2513 type == 1但是2514还是不能删，应该将2513的type改为2
	//可能还有后续...

	set<int> reservedJUMPDESTs;
	for (auto& inv : invRelatedInstrStart) {
		auto invIter = instructions.find(inv.first);
		invIter--;
		string jumpi = invIter->second; assert(jumpi == "JUMPI"); invIter--;
		string pushAddr = invIter->second; assert(pushAddr.find("PUSH" + to_string(getAddrSize())) != string::npos);
		vector<string> temp;
		boost::split(temp, pushAddr, boost::is_any_of(" "));
		int tagAddr = -1;
		SSCANF(temp[1].c_str(), "%x", &tagAddr);
		if (tagAddr == inv.first + 1)//可以顺序删除INVALID指令下的JUMPDEST指令
			invTypes.insert(make_pair(inv.first, 1));
		else {
			reservedJUMPDESTs.insert(tagAddr);
			invTypes.insert(make_pair(inv.first, 2));
		}
	}

	//即使定位到的冗余序列是连续的，也不一定能完全删除
	//示例如下：
	//3128 : DUP2
	//3129 : ISZERO
	//3130 : ISZERO
	//3131 : PUSH2 0x0ae3
	//3134 : JUMPI
	//3135 : INVALID
	//3136 : JUMPDEST
	//以上为3135处assertion的冗余序列，可以看到3131处 push的地址并不是INVALID的下一条地址，相反3136还有其他地方需要其跳转
	//所以以上可删的部分为3128、3129、3130，3135并且将3134处的JUMPI指令改为JUMP


	for (auto& bb : blockNodeIDs)
		if (blocks.at(bb.first).getJumpType() == BlockType::INVALID) {
			size_t allIDNum = bb.second.size();
			size_t partReNum = 0;
			if (invAddr2IDs.find(bb.first) != invAddr2IDs.end())
				partReNum = invAddr2IDs.at(bb.first).size();
			cout << bb.first << "\t" << allIDNum << "\t" << partReNum << endl;
		}

	//cout << invRelatedInstrStart.size() << endl;
	//for (auto& id : redundantInvs) {
	//	int addr = runtimeNodes.at(id).getStart();
	//	cout << id << "\t" << addr << "\t" << invRelatedInstrStart.at(addr) << endl;
	//}

	vector<string> stack;
	set<int> pushTags;
	map<int, int> push2JumpMap;
	set<int> JUMPDESTs; genJUMPDESTs(JUMPDESTs);
	set<vector<string>> IDVisited;
	genPushTags(runtimeNodes, 0, stack, getAddrSize(), JUMPDESTs, pushTags, push2JumpMap, IDVisited);

	map<int, set<int>> addr2PushTags;//存储JUMPDEST地址 => 所有push该地址的指令地址
	for (auto& i : pushTags) {
		string opcode = instructions.find(i)->second;
		vector<string> temp;
		boost::split(temp, opcode, boost::is_any_of(" "));
		int destAddr = -1;
		SSCANF(temp[1].c_str(), "%x", &destAddr);
		addr2PushTags[destAddr].insert(i);
	}
	for (auto& inv : invTypes) {
		if (inv.second == 1)
			if (reservedJUMPDESTs.find(inv.first + 1) != reservedJUMPDESTs.end())
				inv.second = 2;
			else if (addr2PushTags.at(inv.first + 1).size() > 1)//冗余序列之外还有其他地方跳转到INVALID之后的JUMPDEST
				inv.second = 2;
	}

	set<int> potentialTgt;
	genFuncInTgt(runtimeNodes, blocks, potentialTgt);

	map<int, map<int, tuple<int, int>>> IDAddrs;
	map<int, map<int, int>> funcEnds;
	map<int, map<int, vector<int>>> funcTopLevelIDs;
	for (auto& in : potentialTgt) {
		if (IDAddrs.find(in) != IDAddrs.end())
			continue;
		int firstID = *blockNodeIDs.at(in).begin();
		map<int, vector<int>> left;
		map<int, vector<int>> funcIDs;
		genFuncbodyBlocks(runtimeNodes, in, firstID, IDAddrs, funcEnds, funcTopLevelIDs, potentialTgt, 0, left, funcIDs);
	}

	//generateTagInstrsFile(name + ".tag.runtime", pushTags);
	map<int, string> optimizedInstrs;
	string bytecode;

	//与CODECOPY指令相关的offset和size的push地址
	map<int, int> offsetInstrAddrs;
	map<int, int> sizeInstrAddrs;
	map<int, int> codecopyBlocks;
	genCODECOPYOffsetAndSizeInstrs(blocks, codecopyBlocks, offsetInstrAddrs, sizeInstrAddrs);
	cout << setw(20) << "CODECOPY Addr" << setw(20) << "Block" << setw(20) << "Code Offset Addr" << setw(20) << "Code Size Addr" << endl;
	for (auto& c : codecopyBlocks) {
		string offsetAddr = offsetInstrAddrs.find(c.first) == offsetInstrAddrs.end() ? "/" : to_string(offsetInstrAddrs.at(c.first));
		string sizeAddr = sizeInstrAddrs.find(c.first) == sizeInstrAddrs.end() ? "/" : to_string(sizeInstrAddrs.at(c.first));
		cout << setw(20) << c.first << setw(20) << c.second << setw(20) << offsetAddr << setw(20) << sizeAddr << endl;
	}

	z3::context codecopyCtx;
	map<int, vector<expr>> codecopy2OffsetAndSizeExpr = getCODECOPYOffsetAndSizeExpr(blocks, codecopyBlocks, codecopyCtx);
	for (auto& c : codecopy2OffsetAndSizeExpr) {
		cout << "runtime CODECOPY Address : " << c.first << endl;
		string start = c.second[0].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[0].to_string().substr(2))) : c.second[0].to_string();
		string size = c.second[1].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[1].to_string().substr(2))) : c.second[1].to_string();
		cout << "\tcopy start : " << start << endl;
		cout << "\tcopy size : " << size << endl;
	}

	int preCleanRuntimeSize = instructions.rbegin()->first + getOpcodeSize(instructions.rbegin()->second);
	map<int, int>oldCodecopyAddr2NewOffset;

	//冗余sload优化所需数据结构
	map<int, BlockInstrsChanges*> block2InstrChanges;
	map<int, BlockInstrsChanges*> nodeID2Changes;
	set<int> sloadPartReIDs;

	optimize(runtimeNodes, edges, blocks, invAddrs, invIDs, IDAddrs, funcEnds, funcTopLevelIDs, instructions, invRelatedInstrStart, invTypes, JUMPDESTs, push2JumpMap, name, optimizedInstrs,
		block2InstrChanges, nodeID2Changes, sloadPartReIDs,
		codecopyBlocks, offsetInstrAddrs, sizeInstrAddrs, preCleanRuntimeSize, oldCodecopyAddr2NewOffset);
	genBytecode(optimizedInstrs, bytecode);

	//测试CODECOPY相关的offset是否改变的正确
	string newRuntime = bytecode + swarmHash;
	string oldRuntime = runtime + swarmHash;
	//这里由于假设copy data的大小不变因此只需要比较offset之后的数据是否相同即可
	//oldCodecopyAddr2NewOffsetAddr不包含offset指令处为CODESIZE的情况
	for (auto& codecopyAddr : oldCodecopyAddr2NewOffset) {
		int newOffset = codecopyAddr.second;
		int oldOffsetAddr = offsetInstrAddrs.at(codecopyAddr.first);
		vector<string> temp;
		boost::split(temp, instructions.at(oldOffsetAddr), boost::is_any_of(" "));
		int oldOffset = -1;
		SSCANF(temp[1].c_str(), "%x", &oldOffset);
		assert(oldRuntime.substr(oldOffset * 2) == newRuntime.substr(newOffset * 2));
	}

	//开始处理deploy instr中的CODECOPY问题
	genInstrs(constructor, deployInstrs);
	genBasicBlocks(deployInstrs, deployBlocks);
	//与CODECOPY指令相关的offset和size的push地址
	map<int, int> deployCodecopyOffsetInstrAddrs;
	map<int, int> deployCodecopySizeInstrAddrs;
	map<int, int> deployCodecopyBlocks;
	genCODECOPYOffsetAndSizeInstrs(deployBlocks, deployCodecopyBlocks, deployCodecopyOffsetInstrAddrs, deployCodecopySizeInstrAddrs);
	codecopy2OffsetAndSizeExpr.clear();
	codecopy2OffsetAndSizeExpr = getCODECOPYOffsetAndSizeExpr(deployBlocks, deployCodecopyBlocks, codecopyCtx);
	for (auto& c : codecopy2OffsetAndSizeExpr) {
		cout << "deploy CODECOPY Address : " << c.first << endl;
		string start = c.second[0].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[0].to_string().substr(2))) : c.second[0].to_string();
		string size = c.second[1].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[1].to_string().substr(2))) : c.second[1].to_string();
		cout << "\tcopy start : " << start << endl;
		cout << "\tcopy size : " << size << endl;
	}
	//deploy一般情况下也只需要改动offset
	//只有一种情况需要改动size，就是在最后codecopy runtime的时候，目前我们假设当offset和size均对应于copy runtime的时候才改变size(注意此时不改变offset)
	//其他情况下改动offset

	bool debug = true;
	map<int, int> oldcopyAddr2oldOffset;
	map<int, int> oldcopyAddr2newOffset;
	map<int, int> oldcopyAddr2oldSize;
	map<int, int> oldcopyAddr2newSize;
	for (auto& c : deployCodecopyBlocks) {
		//注意只需要改动size的时候offset应该也存在
		if (deployCodecopyOffsetInstrAddrs.find(c.first) != deployCodecopyOffsetInstrAddrs.end()) {
			int offsetAddr = deployCodecopyOffsetInstrAddrs.at(c.first);
			if (deployInstrs.at(offsetAddr) == "CODESIZE")
				continue;
			vector<string> temp;
			boost::split(temp, deployInstrs.at(offsetAddr), boost::is_any_of(" "));
			int offset = -1;
			SSCANF(temp[1].c_str(), "%x", &offset);
			if (size_t(offset * 2) == constructor.length()) {
				//由于deploy的时候可能有参数的缘故，所以并不一定constructor后的所有指令序列均会被codecopy（最后面可能还有构造函数参数序列）
				//因此size的大小不具备参考性，这里仅用offset的判断条件：offset为runtime的开始位置时默认为copy runtime
				int sizeAddr = deployCodecopySizeInstrAddrs.at(c.first);
				string pushInstr = deployInstrs.at(sizeAddr);
				size_t blankIdx = pushInstr.find(' ');
				string push = pushInstr.substr(0, blankIdx);
				int pushSize = stoi(push.substr(4));
				int pushValue = -1;
				SSCANF(pushInstr.substr(blankIdx + size_t(1)).c_str(), "%x", &pushValue);

				int newValue = int(newRuntime.length() - oldRuntime.length()) / 2 + pushValue;
				stringstream ss;
				ss << hex << newValue;
				string newSize;
				ss >> newSize;
				assert(pushSize * 2 >= newSize.length());
				for (int t = (int)newSize.length(); t < pushSize * 2; t++)
					newSize = "0" + newSize;
				newSize = "0x" + newSize;
				if (debug)
					cout << sizeAddr << " before : " << deployInstrs.at(sizeAddr) << ", after : " << push << " " << newSize << endl;
				deployInstrs.at(sizeAddr) = push + " " + newSize;

				oldcopyAddr2oldOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2newOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2oldSize.insert(make_pair(c.first, pushValue));
				oldcopyAddr2newSize.insert(make_pair(c.first, newValue));
			}
			else {
				int newOffset = int(newRuntime.length() - oldRuntime.length()) / 2 + offset;
				stringstream ss;
				ss << hex << newOffset;
				string newOffsetHexStr;
				ss >> newOffsetHexStr;
				int pushSize = stoi(temp[0].substr(4));
				assert(pushSize * 2 >= newOffsetHexStr.length());
				for (int t = (int)newOffsetHexStr.length(); t < pushSize * 2; t++)
					newOffsetHexStr = "0" + newOffsetHexStr;
				newOffsetHexStr = "0x" + newOffsetHexStr;

				if (debug)
					cout << offsetAddr << " before : " << deployInstrs.at(offsetAddr) << ", after : " << temp[0] << " " << newOffsetHexStr << endl;
				deployInstrs.at(offsetAddr) = temp[0] + " " + newOffsetHexStr;

				oldcopyAddr2oldOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2newOffset.insert(make_pair(c.first, newOffset));
			}
		}
	}
	string newConstructor;
	genBytecode(deployInstrs, newConstructor);
	string newBin = newConstructor + newRuntime;
	string oldBin = constructor + oldRuntime;
	for (auto changedcopy : oldcopyAddr2oldOffset) {
		if (oldcopyAddr2oldSize.find(changedcopy.first) == oldcopyAddr2oldSize.end())
			assert(oldBin.substr(changedcopy.second * 2) == newBin.substr(oldcopyAddr2newOffset.at(changedcopy.first) * 2));
	}

	//solidity编译器的不同版本会导致出现不同的目录分隔符
	char c = '\0';
	if (name.find('/') != string::npos)
		c = '/';
	else {
		assert(name.find('\\') != string::npos);
		c = '\\';
	}
	string contractDir = name.substr(0, name.find_last_of(c) + 1);
	//ofstream optimizeBin(contractDir + getAddress() + ".opevm");
	ofstream optimizeBin(contractDir + ".opevm");
	if (!optimizeBin) {
		cerr << "Fail to open" << (contractDir + getAddress() + ".opevm") << endl;
		exit(-1);
	}
	optimizeBin << bytecode << endl;
	optimizeBin.close();

	ofstream newBinFile(contractDir + "newBin");
	newBinFile << newBin << endl;
	newBinFile.close();
}

//instr addr : decimal, pushValue hex(start with 0x)
void Contract::generateDisasm(const map<int, string>& instrs, string fileName) {
	ofstream outFile(fileName);
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	for (auto& instr : instrs)
		outFile << instr.first << " : " << instr.second << endl;
	outFile.close();
}
void Contract::generateDotGraph(const map<int, ECFGNode>& nodes, string fileName, const map<int, vector<string>>& instrSrcmapRuntime) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : nodes) {
		string blockName = "Node_" + to_string(n.first);
		string label = "Node_" + to_string(n.first) + "#" + to_string(n.second.getStart()) + "-" + to_string(n.second.getEnd());
		//label += "#" + n.second.getJumpIn();
		//label = "";
		string color = "";
		if (n.second.getBlockType() == BlockType::INVALID)
			color = ", color = red";

		//测试是否所有的只能通过JUMP指令跳转的基本块都是JUMP[in]或JUMP[out]的跳转目标
		bool onlyJump = true;
		for (auto pnt : n.second.getParents())
			if (pnt == -1) {//start node
				onlyJump = false;
				break;
			}
			else if (nodes.at(pnt).getBlockType() == BlockType::JUMPI || nodes.at(pnt).getBlockType() == BlockType::CREATE ||
				nodes.at(pnt).getBlockType() == BlockType::MESSAGECALL || nodes.at(pnt).getBlockType() == BlockType::NATURAL) {
				onlyJump = false;
				break;
			}
		if (onlyJump)
			color += ", fontcolor = green";

		if (instrSrcmapRuntime.at(n.second.getEnd())[3] == "i")
			color += ", color = blue";
		else if (instrSrcmapRuntime.at(n.second.getEnd())[3] == "o")
			color += ", color = yellow";

		string nodeLabel = "[label = \"" + label + "\"" + color + "]";
		//string nodeLabel = "";
		dotFile += blockName + nodeLabel + "\r\n";
		for (auto p : n.second.getParents()) {
			if (p == -1)
				continue;
			string parentName = "Node_" + to_string(p);
			dotFile += "\t" + parentName + " -> " + blockName + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}
void Contract::genCFGEdges(map<int, ECFGNode>& nodes) {//generate every node's jumpID(jump target CFGNode ID) and fallsID(natural target CFGNodeID)
	for (auto& n : nodes) {
		set<int> parents = n.second.getParents();
		for (int p : parents) {
			if (p == -1)//start block
				continue;
			if (nodes.at(p).getJumpAddr() == n.second.getStart())
				nodes.at(p).setJumpID(n.first);
			else
				nodes.at(p).setFallsID(n.first);
		}
	}
}

void displayInstrExprStack(const vector<Expr>& exprs) {
	for (auto& e : exprs)
		e.print();
}
//void processSymExpr(string& symExpr, bool symbolic) {
//	if (symbolic) {
//		map<string, int>& exprDepth = StackFrame::exprDepth;
//		if (exprDepth.find(symExpr) == exprDepth.end()) {
//			exprDepth.insert(make_pair(symExpr, 0));
//			symExpr += "!0";
//		}
//		else
//			symExpr += "!" + to_string(exprDepth.at(symExpr));
//	}
//}

void displayStackFrame(const vector<StackFrame>& stack) {
	displayBlueMsg("==================");
	for (size_t i = 0; i < stack.size(); i++) {
		string sym;
		//if (stack[i].symbolic)
		//	sym = "sym";
		//else
		//	sym = "nonsym";
		cout << i << " " << setw(6) << sym << " ";
		displayBlueMsg(stack[i].z3Expr.to_string());
	}
	displayBlueMsg("TOP");
	displayBlueMsg("==================");
}

void calScc(const map<int, set<int>>& edges, map<int, set<int>>& scc) {
	map<int, set<int>> reEdges;
	set<int> visited;
	set<int> loop;
	for (auto& i : edges) {
		if (i.second.find(i.first) != i.second.end())//加入自环节点
			loop.insert(i.first);

		if (reEdges.find(i.first) == reEdges.end())
			reEdges[i.first] = { };
		for (auto& n : i.second)
			reEdges[n].insert(i.first);
	}

	//calculate post order of G
	vector<int> po;
	for (auto& i : edges) {
		postDFS(i.first, edges, visited, po);
	}

	//calculate reverse post order of G
	vector<int> rpo;
	for (auto iter = po.rbegin(); iter != po.rend(); iter++)
		rpo.push_back(*iter);

	//计算强连通分量
	visited.clear();
	for (auto& i : rpo) {
		vector<int> stack;
		postDFS(i, reEdges, visited, stack);
		//当节点i之前已被遍历过，stack可能为空
		if (stack.empty())
			continue;
		int back = stack.back();
		assert(scc.find(back) == scc.end());
		scc[back] = { };
		for (auto& n : stack) {
			scc.at(back).insert(n);
		}
	}
}

void genLoopRelNodes(const map<int, set<int>>& edges, map<int, set<int>>& scc, set<int>& visited) {
	for (auto& s : scc)
		//第一种情况为正常循环情况
		//第二种情况包含自环
		if (s.second.size() >= 2 || edges.at(s.first).find(s.first) != edges.at(s.first).end()) {
			int startNodeID = s.first;
			queue<int> que;
			que.push(startNodeID);
			visited.insert(startNodeID);
			while (!que.empty()) {
				int front = que.front();
				que.pop();
				for (auto& chd : edges.at(front))
					if (visited.find(chd) == visited.end()) {
						visited.insert(chd);
						que.push(chd);
					}
			}
		}
}
void genDomTree(map<int, int>& IDom, map<int, set<int>>& dTree) {
	//Step 3 : generate dominator tree from IDom
	for (auto& id : IDom)
		dTree[id.first] = {};
	for (auto& id : IDom) {
		if (id.second != -1)
			dTree[id.second].insert(id.first);
	}
}
//已知所有经过节点n的路径均为经过节点IDom(n)
//那么在反向CFG中所有从节点n的出发路径均会经过IDom(n)
//所以从节点n开始遍历直到遍历到节点IDom(n)即能得到反向的子图
//将反向子图再反向，即能得到所要进行符号执行的最小子图
//注意该方法只有在id不是循环体头部，结果才正确
void genPartEdges(const map<int, set<int>>& reEdges, int idom, int id, map<int, set<int>>& res) {
	set<int> visited;
	queue<int> que;
	que.push(id);
	visited.insert(id);
	while (!que.empty()) {
		int front = que.front();
		que.pop();
		for (auto& pnt : reEdges.at(front))
			if (visited.find(pnt) == visited.end() && pnt != idom) {
				que.push(pnt);
				visited.insert(pnt);
			}
	}
	//visited不包idom节点
	map<int, set<int>> reRes;
	for (auto& i : visited)
		reRes[i] = reEdges.at(i);
	reRes[idom] = {};
	for (auto& i : reRes) {
		if (res.find(i.first) == res.end())
			res[i.first] = {};
		for (auto& pnt : i.second)
			res[pnt].insert(i.first);
	}
}


////不能使用reEdges从id节点开始层序遍历到idom(id)节点，这是因为在id节点为循环相关节点时会生成多余节点
////应该使用edges并从idom节点dfs到id，然后把路径上的所有点保存下来为集合s1，然后将s1中的所有节点所在的强连通分量的所有节点加入s1，形成res的点集
////然后将res中的所有点之间的边加入res的边集
//void genPartEdges(map<int, set<int>>& reEdges, int idom, int id, const map<int, set<int>>& scc, map<int, set<int>>& res) {
//	vector<int> stack;
//	stack.push_back(id);
//	set<int> visited;
//	visited.insert(id);
//	set<int> partNodes;//CFG中从idom(id)节点到id节点的路径上所有相关的节点
//	while (!stack.empty()) {
//		int top = stack.back();
//		if (top == idom) {
//			for (auto& n : stack)
//				partNodes.insert(n);
//			visited.erase(id);
//			stack.pop_back();
//		}
//		else {
//			bool flag = false;
//			for (auto& c : reEdges.at(top))
//				if (visited.find(c) == visited.end()) {
//					if (c == idom && partNodes.find(top) != partNodes.end())//
//						continue;
//					stack.push_back(c);
//					visited.insert(c);
//					flag = true;
//					break;
//				}
//			if (!flag)
//				stack.pop_back();
//		}
//	}
//
//}

string symbolicPrefix = "symbolic_stack";


static map<string, set<CFGLoc>> storageInstrs;//st_index => 读写storage的位置信息
static set<int> SSTOREsymInstrs;//生成SSTORE指令时st_index的index是symbolic value
static map<CFGLoc, string> speSload;//sload的位置信息 => sload到栈中的具体的值（未测试过是否在真实场景中出现执行SLOAD指令时load的是常数）
void Contract::symExecInstr(int NodeID, int pc, string instr, vector<StackFrame>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, map<int, ECFGNode>& nodes) {
	using boost::multiprecision::uint256_t;
	using boost::multiprecision::int256_t;
	using boost::multiprecision::uint512_t;
	vector<string> instrParts;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string mnemonic = instrParts[0];
	int opcode = Opcode::getOpcode(mnemonic);
	const size_t top = stack.size() - 1;

	static int callNum = 0;
	static int createNum = 0;
	int beforeStackSize = static_cast<int>(stack.size());
	switch (opcode) {
	case 0x00:break;//STOP
	case 0x01: {//ADD
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() + stack[top - 1].getValue());
			Expr add(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, add);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr add(256, two.getExpr(), stack[top].getExpr(), "add", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, add);
		}

		two.z3Expr = (stack[top].z3Expr + stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x02: {//MUL
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() * stack[top - 1].getValue());

			Expr mul(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, mul);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr mul(256, two.getExpr(), stack[top].getExpr(), "mul", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, mul);
		}
		if (stack[top].z3Expr.is_bool())
			stack[top].z3Expr = z3::ite(stack[top].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256));
		if (stack[top - 1].z3Expr.is_bool())
			stack[top - 1].z3Expr = z3::ite(stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256));
		two.z3Expr = (stack[top].z3Expr * stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x03: {//SUB
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() - stack[top - 1].getValue());

			Expr sub(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, sub);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr sub(256, two.getExpr(), stack[top].getExpr(), "sub", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, sub);
		}
		two.z3Expr = (stack[top].z3Expr - stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x04: {//DIV
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			if (stack[top - 1].getUnsignedValue() == 0)
				two.setValue(0);
			else
				two.setValue(stack[top].getUnsignedValue() / stack[top - 1].getUnsignedValue());

			Expr div(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, div);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr div(256, two.getExpr(), stack[top].getExpr(), "div", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, div);
		}
		two.z3Expr = z3::udiv(stack[top].z3Expr, stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x05: {//SDIV
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		//Note : uint256_t=>int256_t convertion does not change the underlying encoding and meaning
		//int256_t => uint256_t must be explicit
		//uint256_t => int256_t can be implicit
		//eg :	uint256_t u = -1;
		//			int256_t i = (uint256_t)u;//here i's meaning is 2^256 - 1
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			int256_t first = stack[top].getValue();
			int256_t second = stack[top - 1].getValue();
			int256_t min = -boost::multiprecision::pow(int256_t(2), 255);
			int256_t result = 0;
			if (second != 0)
				if (first == min && second == -1)
					result = min;
				else
					result = ((first / second) > 0 ? 1 : -1) * (abs(first) / abs(second));

			two.setValue(result);

			Expr sdiv(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, sdiv);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr sdiv(256, two.getExpr(), stack[top].getExpr(), "sdiv", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, sdiv);
		}
		two.z3Expr = (stack[top].z3Expr / stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x06: {//MOD
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			if (stack[top - 1].getValue() == 0)
				two.setValue(0);
			else
				two.setValue(stack[top].getUnsignedValue() % stack[top - 1].getUnsignedValue());

			Expr mod(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, mod);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr mod(256, two.getExpr(), stack[top].getExpr(), "mod", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, mod);
		}
		two.z3Expr = z3::ite(stack[top - 1].z3Expr == 0, StackFrame::c.bv_val(0, 256), z3::urem(stack[top].z3Expr, stack[top - 1].z3Expr)).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x07: {//SMOD
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);

			int256_t first = stack[top].getValue();
			int256_t second = stack[top - 1].getValue();

			//sCompile contradicts yellow paper in SMOD
			//sCompile s0' = sign(s0 / s1)(|s0| mod |s1|)
			//yellow paper s0' = sign(s0)(|s0| mod |s1|)
			//yellow paper's definition used here
			//boost::multiprecision::int256_t result = ((first / second) > 0 ? 1 : -1) * (abs(first) % abs(second));
			int256_t result = 0;
			if (second != 0)
				result = (first > 0 ? 1 : -1) * (abs(first) % abs(second));
			two.setValue(result);

			Expr smod(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, smod);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr smod(256, two.getExpr(), stack[top].getExpr(), "smod", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, smod);
		}
		//z3::abs can't be used on bit-vectors
		z3::expr absS0 = ite(stack[top].z3Expr < 0, -stack[top].z3Expr, stack[top].z3Expr);
		z3::expr absS1 = ite(stack[top - 1].z3Expr < 0, -stack[top - 1].z3Expr, stack[top - 1].z3Expr);

		z3::expr modRes = z3::ite(stack[top].z3Expr > StackFrame::c.bv_val(0, 256), z3::urem(absS0, absS1), -z3::urem(absS0, absS1)).simplify();
		two.z3Expr = modRes;
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x08: {//ADDMOD
		StackFrame three;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF && stack[top - 2].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT && stack[top - 2].getType() == StackType::CONSTANT) {
			three.setType(StackType::CONSTANT);
			uint512_t imRes = (stack[top].getUnsignedValue().convert_to<uint512_t>() + stack[top - 1].getUnsignedValue().convert_to<uint512_t>()) % stack[top - 2].getUnsignedValue().convert_to<uint512_t>();
			three.setValue(imRes.convert_to<uint256_t>());

			Expr addmod(256, "mu_S_" + to_string(top - 2), three.getExpr());
			nodes.at(NodeID).addExpr(pc, addmod);
		}
		else {
			three.setType(StackType::EXPR);
			three.setName("mu_S_" + to_string(top - 2));

			//!? All intermediate calculations are not subject to the 2^256 modulo
			//!? temp512_num512'1 = zext mu_S_0 256
			//!? temp512_num512'2 = zext mu_S_1 256
			//!? temp512_num512'3 = zext mu_S_2 256
			//!? temp512_num512'4 = temp512_num512'1 + temp512_num512'2
			//!? temp512_num512'5 = temp512_num512'4 mod temp512_num512'3
			//!? mu_S_0' = truncate temp512_num512'5 256
			//! getNum512() has side effect : num512 plus 1 every time getNum512() called
			string temp1 = "temp512_" + to_string(Operand::getNum512());
			string temp2 = "temp512_" + to_string(Operand::getNum512());
			string temp3 = "temp512_" + to_string(Operand::getNum512());
			string temp4 = "temp512_" + to_string(Operand::getNum512());
			string temp5 = "temp512_" + to_string(Operand::getNum512());
			nodes.at(NodeID).addExpr(pc, Expr(512, temp1, stack[top].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp2, stack[top - 1].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp3, stack[top - 2].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp4, temp1, "add", temp2));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp5, temp4, "mod", temp3));
			nodes.at(NodeID).addExpr(pc, Expr(512, three.getExpr(), temp5, "truncate", "256"));
		}
		expr zero = StackFrame::c.bv_val(0, 1);
		if (stack[top - 2].z3Expr.is_numeral() && stack[top - 2].z3Expr.get_decimal_string(256) == "0")
			three.z3Expr = zero;
		else {
			z3::expr x = z3::concat(zero, stack[top].z3Expr);
			z3::expr y = z3::concat(zero, stack[top - 1].z3Expr);
			z3::expr z = z3::concat(zero, stack[top - 2].z3Expr);
			three.z3Expr = z3::ite(stack[top - 2].z3Expr == 0, StackFrame::c.bv_val(0, 256), z3::urem(x + y, z).extract(255, 0)).simplify();
		}
		//three.symbolic = stack[top].symbolic || stack[top - 1].symbolic || stack[top - 2].symbolic;
		stack[top - 2] = three;
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x09: {//MULMOD
		StackFrame three;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF && stack[top - 2].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT && stack[top - 2].getType() == StackType::CONSTANT) {
			three.setType(StackType::CONSTANT);
			uint512_t imRes = (stack[top].getUnsignedValue().convert_to<uint512_t>() * stack[top - 1].getUnsignedValue().convert_to<uint512_t>()) % stack[top - 2].getUnsignedValue().convert_to<uint512_t>();
			three.setValue(imRes.convert_to<uint256_t>());

			Expr mulmod(256, "mu_S_" + to_string(top - 2), three.getExpr());
			nodes.at(NodeID).addExpr(pc, mulmod);
		}
		else {
			three.setType(StackType::EXPR);
			three.setName("mu_S_" + to_string(top - 2));

			//!? All intermediate calculations are not subject to the 2^256 modulo
			//!? temp512_num512'1 = zext mu_S_0 256
			//!? temp512_num512'2 = zext mu_S_1 256
			//!? temp512_num512'3 = zext mu_S_2 256
			//!? temp512_num512'4 = temp512_num512'1 * temp512_num512'2
			//!? temp512_num512'5 = temp512_num512'4 mod temp512_num512'3
			//!? mu_S_0' = truncate temp512_num512'5 256
			//! getNum512() has side effect : num512 plus 1 every time getNum512() called
			string temp1 = "temp512_" + to_string(Operand::getNum512());
			string temp2 = "temp512_" + to_string(Operand::getNum512());
			string temp3 = "temp512_" + to_string(Operand::getNum512());
			string temp4 = "temp512_" + to_string(Operand::getNum512());
			string temp5 = "temp512_" + to_string(Operand::getNum512());
			nodes.at(NodeID).addExpr(pc, Expr(512, temp1, stack[top].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp2, stack[top - 1].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp3, stack[top - 2].getExpr(), "zext", "256"));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp4, temp1, "mul", temp2));
			nodes.at(NodeID).addExpr(pc, Expr(512, temp5, temp4, "mod", temp3));
			nodes.at(NodeID).addExpr(pc, Expr(512, three.getExpr(), temp5, "truncate", "256"));
		}

		expr zero = StackFrame::c.bv_val(0, 256);
		if (stack[top - 2].z3Expr.is_numeral() && stack[top - 2].z3Expr.get_decimal_string(256) == "0")
			three.z3Expr = zero;
		else {
			z3::expr x = z3::concat(zero, stack[top].z3Expr);
			z3::expr y = z3::concat(zero, stack[top - 1].z3Expr);
			z3::expr z = z3::concat(zero, stack[top - 2].z3Expr);
			three.z3Expr = z3::ite(stack[top - 2].z3Expr == zero, zero, z3::urem(x * y, z).extract(255, 0)).simplify();
		}
		//three.symbolic = stack[top].symbolic || stack[top - 1].symbolic || stack[top - 2].symbolic;
		stack[top - 2] = three;
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x0a: {//EXP
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			//int256_t pow(int256_t, unsigned int)
			//幂指数太大计算结果也无意义，一般情况下指数的大小不会超过32位
			uint256_t res = bm::pow(stack[top].getUnsignedValue(), stack[top - 1].getUnsignedValue().convert_to<unsigned int>());
			two.setValue(res);

			two.z3Expr = StackFrame::genZ3Expr(res);
			Expr exp(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, exp);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr exp(256, two.getExpr(), stack[top].getExpr(), "exp", stack[top - 1].getExpr());//? exp or pow
			two.z3Expr = StackFrame::c.bv_const(("exp#" + stack[top].z3Expr.to_string() + "#" + stack[top - 1].z3Expr.to_string()).c_str(), 256);
			nodes.at(NodeID).addExpr(pc, exp);
		}
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x0b: {//SIGNEXTEND
		//! Note : SIGNEXTEND only handles concrete values
		//! if operands contatin symbolic value, feedback a warning
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			int256_t first = stack[top].getValue();
			int256_t second = stack[top - 1].getValue();
			if (first >= 32 || first <= 0)
				two.setValue(second);
			else {
				unsigned int signedBitsFromRight = (8 * first + 7).convert_to<unsigned int>();
				int256_t flag = ((int256_t)1) << signedBitsFromRight;
				int256_t sign = flag & second;
				if (sign == 0) {//signed_bit = 0,mask  000...01...111 
					int256_t mask = flag - 1;
					two.setValue(mask & second);
				}
				else {//mask 111...10...000
					int256_t mask = ~(flag - 1);
					two.setValue(mask | second);
				}
			}

			Expr signextend(256, "mu_S_" + to_string(top - 1), two.getExpr());
			two.z3Expr = StackFrame::c.bv_val(two.getExpr().c_str(), 256);
			nodes.at(NodeID).addExpr(pc, signextend);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			string right = "signextend#" + stack[top].z3Expr.to_string() + "#" + stack[top - 1].z3Expr.to_string();
			two.z3Expr = StackFrame::c.bv_const(right.c_str(), 256);
			//processSymExpr(right, stack[top].symbolic || stack[top - 1].symbolic);
			Expr signextend(256, two.getExpr(), right);

			nodes.at(NodeID).addExpr(pc, signextend);
			//cout << "SIGNEXTEND encounters SYMBOLIC VALUES" << endl;

		}
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}

	case 0x10: {//LT
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getUnsignedValue() < stack[top - 1].getUnsignedValue() ? 1 : 0);

			Expr lt(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, lt);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr lt(256, two.getExpr(), stack[top].getExpr(), "lt", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, lt);
		}

		two.z3Expr = z3::ult(stack[top].z3Expr, stack[top - 1].z3Expr).simplify();
		//two.z3Expr = z3::ite(z3::ult(stack[top].z3Expr, stack[top - 1].z3Expr), StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x11: {//GT
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getUnsignedValue() > stack[top - 1].getUnsignedValue() ? 1 : 0);

			Expr gt(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, gt);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr gt(256, two.getExpr(), stack[top].getExpr(), "gt", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, gt);
		}

		two.z3Expr = z3::ugt(stack[top].z3Expr, stack[top - 1].z3Expr).simplify();
		//two.z3Expr = z3::ite(z3::ugt(stack[top].z3Expr, stack[top - 1].z3Expr), StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x12: {//SLT
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() < stack[top - 1].getValue() ? 1 : 0);

			Expr slt(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, slt);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr slt(256, two.getExpr(), stack[top].getExpr(), "slt", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, slt);
		}

		two.z3Expr = (stack[top].z3Expr < stack[top - 1].z3Expr).simplify();
		//two.z3Expr = z3::ite(stack[top].z3Expr < stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x13: {//SGT
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() > stack[top - 1].getValue() ? 1 : 0);

			Expr sgt(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, sgt);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr sgt(256, two.getExpr(), stack[top].getExpr(), "sgt", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, sgt);
		}

		two.z3Expr = (stack[top].z3Expr > stack[top - 1].z3Expr).simplify();
		//two.z3Expr = z3::ite(stack[top].z3Expr > stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x14: {//EQ
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() == stack[top - 1].getValue() ? 1 : 0);

			Expr eq(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, eq);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr eq(256, two.getExpr(), stack[top].getExpr(), "eq", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, eq);
		}

		//存在常数1(bv)与bool expr的比较
		if ((stack[top].z3Expr.is_bv() && stack[top - 1].z3Expr.is_bv()) || (stack[top].z3Expr.is_bool() && stack[top - 1].z3Expr.is_bool()))
			two.z3Expr = (stack[top].z3Expr == stack[top - 1].z3Expr).simplify();
		else {
			expr bvExper(StackFrame::c);
			expr other(StackFrame::c);
			if (stack[top - 1].z3Expr.is_bool()) {
				bvExper = z3::ite(stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256));
				other = stack[top].z3Expr;
			}
			else {
				bvExper = z3::ite(stack[top].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256));
				other = stack[top - 1].z3Expr;
			}
			two.z3Expr = (bvExper == other).simplify();
		}
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x15: {//ISZERO
		StackFrame one;
		assert(stack[top].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT) {
			one.setType(StackType::CONSTANT);
			one.setValue(stack[top].getValue() == 0 ? 1 : 0);

			Expr iszero(256, "mu_S_" + to_string(top), one.getExpr());
			nodes.at(NodeID).addExpr(pc, iszero);
		}
		else {
			one.setType(StackType::EXPR);
			one.setName("mu_S_" + to_string(top));

			Expr iszero(256, one.getExpr(), stack[top].getExpr(), "eq", "0");
			nodes.at(NodeID).addExpr(pc, iszero);
		}
		if (stack[top].z3Expr.is_bool())
			one.z3Expr = (!stack[top].z3Expr).simplify();
		else
			one.z3Expr = z3::ite(stack[top].z3Expr == 0, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)).simplify();
		//one.symbolic = stack[top].symbolic;
		stack[top] = one;
		break;
	}
	case 0x16: {//AND
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() & stack[top - 1].getValue());

			//and标识符已被占用
			Expr AND(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, AND);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr AND(256, two.getExpr(), stack[top].getExpr(), "and", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, AND);
		}
		if (stack[top].z3Expr.is_bool() && stack[top - 1].z3Expr.is_bool())
			two.z3Expr = (stack[top].z3Expr && stack[top - 1].z3Expr).simplify();
		else if (stack[top].z3Expr.is_bv() && stack[top - 1].z3Expr.is_bv())
			two.z3Expr = (stack[top].z3Expr & stack[top - 1].z3Expr).simplify();
		else if (stack[top].z3Expr.is_bool())
			two.z3Expr = (z3::ite(stack[top].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)) & stack[top - 1].z3Expr).simplify();
		else
			two.z3Expr = (z3::ite(stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)) & stack[top].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x17: {//OR
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() | stack[top - 1].getValue());

			Expr OR(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, OR);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr OR(256, two.getExpr(), stack[top].getExpr(), "or", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, OR);
		}
		if (stack[top].z3Expr.is_bv() && stack[top - 1].z3Expr.is_bv())
			two.z3Expr = (stack[top].z3Expr | stack[top - 1].z3Expr).simplify();
		else if(stack[top].z3Expr.is_bool() && stack[top - 1].z3Expr.is_bool())
			two.z3Expr = (stack[top].z3Expr || stack[top - 1].z3Expr).simplify();
		else if(stack[top].z3Expr.is_bool() && stack[top - 1].z3Expr.is_bv())
			two.z3Expr = (z3::ite(stack[top].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)) | stack[top - 1].z3Expr).simplify();
		else
			two.z3Expr = (z3::ite(stack[top - 1].z3Expr, StackFrame::c.bv_val(1, 256), StackFrame::c.bv_val(0, 256)) | stack[top].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x18: {//XOR
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top].getValue() ^ stack[top - 1].getValue());

			Expr XOR(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, XOR);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr XOR(256, two.getExpr(), stack[top].getExpr(), "xor", stack[top - 1].getExpr());
			nodes.at(NodeID).addExpr(pc, XOR);
		}

		two.z3Expr = (stack[top].z3Expr ^ stack[top - 1].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x19: {//NOT
		StackFrame one;
		assert(stack[top].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT) {
			one.setType(StackType::CONSTANT);
			one.setValue(~stack[top].getValue());

			Expr NOT(256, "mu_S_" + to_string(top), one.getExpr());
			nodes.at(NodeID).addExpr(pc, NOT);
		}
		else {
			one.setType(StackType::EXPR);
			one.setName("mu_S_" + to_string(top));

			Expr NOT(256, one.getExpr(), "not", stack[top].getExpr());
			nodes.at(NodeID).addExpr(pc, NOT);
		}

		one.z3Expr = (~stack[top].z3Expr).simplify();
		//one.symbolic = stack[top].symbolic;
		stack[top] = one;
		break;
	}
	case 0x1a: {//BYTE
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			int256_t first = stack[top].getValue();
			int256_t second = stack[top - 1].getValue();
			if (first >= 32)
				two.setValue(0);
			else {
				int256_t mask = ((int256_t)0xff) << ((31 - first.convert_to<unsigned int>()) * 8);
				two.setValue(second & mask);
			}

			Expr byte(256, "mu_S_" + to_string(top - 1), two.getExpr());
			two.z3Expr = StackFrame::c.bv_val(two.getExpr().c_str(), 256);
			nodes.at(NodeID).addExpr(pc, byte);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));
			string right = stack[top].z3Expr.to_string() + "#byte#" + stack[top - 1].z3Expr.to_string();
			//processSymExpr(right, stack[top].symbolic || stack[top - 1].symbolic);
			Expr byte(256, two.getExpr(), right);
			expr ff = StackFrame::c.bv_val(0xff, 256);
			expr shift = stack[top].z3Expr * 8;
			two.z3Expr = (z3::shl(ff, shift) & stack[top - 1].z3Expr).simplify();
			nodes.at(NodeID).addExpr(pc, byte);
		}
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x1b: {//SHL
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top - 1].getValue() << stack[top].getValue().convert_to<unsigned int>());

			Expr SHL(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, SHL);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr SHL(256, two.getExpr(), stack[top - 1].getExpr(), "shl", stack[top].getExpr());
			nodes.at(NodeID).addExpr(pc, SHL);
		}

		two.z3Expr = z3::shl(stack[top - 1].z3Expr, stack[top].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x1c: {//SHR
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);

			two.setValue(stack[top - 1].getUnsignedValue() >> stack[top].getUnsignedValue().convert_to<unsigned int>());

			Expr SHR(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, SHR);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr SHR(256, two.getExpr(), stack[top - 1].getExpr(), "lshr", stack[top].getExpr());
			nodes.at(NodeID).addExpr(pc, SHR);
		}

		two.z3Expr = z3::lshr(stack[top - 1].z3Expr, stack[top].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}
	case 0x1d: {//SAR
		StackFrame two;
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		if (stack[top].getType() == StackType::CONSTANT && stack[top - 1].getType() == StackType::CONSTANT) {
			two.setType(StackType::CONSTANT);
			two.setValue(stack[top - 1].getValue() >> stack[top].getValue().convert_to<unsigned int>());

			Expr SAR(256, "mu_S_" + to_string(top - 1), two.getExpr());
			nodes.at(NodeID).addExpr(pc, SAR);
		}
		else {
			two.setType(StackType::EXPR);
			two.setName("mu_S_" + to_string(top - 1));

			Expr SAR(256, two.getExpr(), stack[top - 1].getExpr(), "ashr", stack[top].getExpr());
			if (LOG_LEVEL == spdlog::level::debug)
				SAR.print();
			assert(nodes.find(NodeID) != nodes.end());
			nodes.at(NodeID).addExpr(pc, SAR);
		}

		two.z3Expr = z3::ashr(stack[top - 1].z3Expr, stack[top].z3Expr).simplify();
		//two.symbolic = stack[top].symbolic || stack[top - 1].symbolic;
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}

	case 0x20: {//SHA3
		StackFrame two("mu_S_" + to_string(top - 1));
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF);
		bool symbolic = false;
		if (stack[top - 1].z3Expr.is_numeral() && stack[top - 1].z3Expr.get_numeral_int() != 0) {//size is numeral
			int offInt = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_numeral_int() : -1;
			int size = stack[top - 1].z3Expr.get_numeral_int();
			expr content = StackFrame::c.bv_val(0, 1);
			int i;
			for (i = 0; i < size; i += 32) {
				string memLoc;
				int end = 0;
				//size可能不是32的整数倍，比如28
				if (i + 32 > size)
					end = size;
				else
					end = i + 32;
				bool memLocSymbolic = false;
				if (stack[top].z3Expr.is_numeral())
					memLoc = to_string(offInt + i) + "$" + to_string(offInt + end);
				else {
					//memLocSymbolic = stack[top].symbolic;
					memLoc = (stack[top].z3Expr + i).simplify().to_string() + "$" + (stack[top].z3Expr + end).simplify().to_string();
				}
				//bool contentSym = false;
				expr mem(StackFrame::c);
				if (memory.find(memLoc) == memory.end()) {
					mem = StackFrame::c.bv_const(("mem_" + memLoc).c_str(), 256);
					//contentSym = memLocSymbolic;
					//if (memLocSymbolic)
					//	StackFrame::exprDepth.insert(make_pair(mem.to_string(), 0));
				}
				else {
					mem = memory.at(memLoc);
					//contentSym = StackFrame::exprDepth.find(mem.to_string()) != StackFrame::exprDepth.end();
				}
				//symbolic |= contentSym;
				content = z3::concat(content, mem);
			}
			//位向量右边为低位
			content = content.extract(i * 8 - 1, i * 8 - size * 8).simplify();
			two.z3Expr = StackFrame::c.bv_const(("sha3#" + content.to_string()).c_str(), 256);

			if (content.to_string().find(symbolicPrefix) != string::npos) {
				//vector<bool> visited;
				//visit(visited, content.simplify(), 0);
			}
		}
		else {//一般见于对string类型的keccak操作
			static int sha3Num = 0;
			two.z3Expr = StackFrame::c.bv_const(("sha3_" + to_string(sha3Num)).c_str(), 256);
			sha3Num++;
		}
		//two.symbolic = symbolic;
		string right = two.z3Expr.to_string();
		//processSymExpr(right, symbolic);
		Expr sha3(256, two.getExpr(), right);
		nodes.at(NodeID).addExpr(pc, sha3);
		stack[top - 1] = two;
		stack.pop_back();
		break;
	}

	case 0x30: {//ADDRESS
		StackFrame Ia("mu_S_" + to_string(top + 1));
		Ia.z3Expr = StackFrame::c.bv_const("Ia", 256);

		Expr address(256, Ia.getExpr(), Ia.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, address);
		stack.push_back(Ia);
		break;
	}
	case 0x31: {//BALANCE
		StackFrame b("mu_S_" + to_string(top));
		string right = ("balance#" + stack[top].z3Expr.to_string()).c_str();
		b.z3Expr = StackFrame::c.bv_const(right.c_str(), 256);
		//b.symbolic = stack[top].symbolic;
		//processSymExpr(right, stack[top].symbolic);
		//s0' = s0's balance(s0 is an address)
		Expr balance(256, b.getExpr(), right);
		nodes.at(NodeID).addExpr(pc, balance);

		stack[top] = b;
		break;
	}
	case 0x32: {//ORIGIN
		StackFrame Io("mu_S_" + to_string(top + 1));
		Io.z3Expr = StackFrame::c.bv_const("Io", 256);

		Expr origin(256, Io.getExpr(), Io.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, origin);

		stack.push_back(Io);
		break;
	}
	case 0x33: {//CALLER
		StackFrame Is("mu_S_" + to_string(top + 1));
		Is.z3Expr = StackFrame::c.bv_const("Is", 256);

		Expr caller(256, Is.getExpr(), Is.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, caller);

		stack.push_back(Is);
		break;
	}
	case 0x34: {//CALLVALUE
		StackFrame Iv("mu_S_" + to_string(top + 1));
		Iv.z3Expr = StackFrame::c.bv_const("Iv", 256);

		Expr callvalue(256, Iv.getExpr(), Iv.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, callvalue);

		stack.push_back(Iv);
		break;
	}
	case 0x35: {//CALLDATALOAD
		assert(stack[top].getType() != StackType::NODEF);
		StackFrame calldata("mu_S_" + to_string(top));
		if (stack[top].getType() == StackType::CONSTANT) {
			Expr e(256, calldata.getExpr(), "Id_" + stack[top].getExpr());
			calldata.z3Expr = StackFrame::c.bv_const(("Id_" + stack[top].getExpr()).c_str(), 256);
			nodes.at(NodeID).addExpr(pc, e);
		}
		else {
			calldata.z3Expr = StackFrame::c.bv_const(("Id_" + stack[top].z3Expr.to_string()).c_str(), 256);
			//calldata.symbolic = stack[top].symbolic;
			string right = calldata.z3Expr.to_string();
			//processSymExpr(right, stack[top].symbolic);
			Expr e(256, calldata.getExpr(), right);
			nodes.at(NodeID).addExpr(pc, e);
		}

		stack[top] = calldata;
		break;
	}
	case 0x36: {//CALLDATASIZE
		StackFrame calldatasize("mu_S_" + to_string(top + 1));
		calldatasize.z3Expr = StackFrame::c.bv_const("Id_size", 256);
		Expr e(256, calldatasize.getExpr(), calldatasize.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(calldatasize);
		break;
	}
	case 0x37: {//CALLDATACOPY
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x38: {//CODESIZE
		StackFrame size("mu_S_" + to_string(top + 1));
		size.z3Expr = StackFrame::c.bv_val((runtime.length() + swarmHash.length()) / 2, 256);

		Expr codesize(256, size.getExpr(), size.z3Expr.get_decimal_string(256));
		nodes.at(NodeID).addExpr(pc, codesize);
		stack.push_back(size);
		break;
	}
	case 0x39: {//CODECOPY
		assert(stack[top].getType() != StackType::NODEF && stack[top - 1].getType() != StackType::NODEF && stack[top - 2].getType() != StackType::NODEF);

		//在确定了CODESIZE之后使用CODECOPY指令时的复制 code offset和code size应该是确定的
		if (stack[top - 1].z3Expr.is_numeral() && stack[top - 2].z3Expr.is_numeral()) {
			uint256_t copysz(stack[top - 2].z3Expr.get_decimal_string(256));
			string complete = runtime + swarmHash;
			if (copysz > complete.size() / 2) {
				stack.pop_back();
				stack.pop_back();
				stack.pop_back();
				break;
			}
			int offset = stack[top - 1].z3Expr.get_numeral_int();
			int size = stack[top - 2].z3Expr.get_numeral_int();
			bool isMemLocNumeral = stack[top].z3Expr.is_numeral();

			for (int i = 0; i < size; i += 32) {
				int end = 0;
				if (i + 32 > size)
					end = size;
				else
					end = i + 32;
				int copyLen = (end - i) * 2;
				string codeSegment = complete.substr(offset * 2, copyLen);
				for (size_t i = codeSegment.length(); i < copyLen; i++)
					codeSegment.push_back('0');
				uint256_t copyCnt("0x" + codeSegment);
				string memLoc;
				//bool memLocSym = false;
				if (isMemLocNumeral) {
					int memOffset = stack[top].z3Expr.get_numeral_int();
					memLoc = to_string(memOffset + i) + "$" + to_string(memOffset + end);
				}
				else {
					//memLocSym = stack[top].symbolic;
					memLoc = (stack[top].z3Expr + i).simplify().to_string() + "$" + (stack[top].z3Expr + end).simplify().to_string();
				}

				//memory[] : the lack of default constructor of z3::expr
				//memory.insert(key, value) or memory.emplace(key, value) can't insert when key already exists
				auto iter = memory.find(memLoc);
				expr copyCntExpr = StackFrame::c.bv_val(boost::lexical_cast<string>(copyCnt).c_str(), 256);
				if (iter == memory.end())
					memory.emplace(make_pair(memLoc, copyCntExpr));
				else
					iter->second = copyCntExpr;
				string left = "mem_" + memLoc;
				//processSymExpr(left, memLocSym);
				Expr codecopy(256, left, copyCntExpr.to_string());
				nodes.at(NodeID).addExpr(pc, codecopy);
			}
		}
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x3a: {//GASPRICE
		StackFrame gasprice("mu_S_" + to_string(top + 1));
		gasprice.z3Expr = StackFrame::c.bv_const("Ip", 256);
		Expr e(256, gasprice.getExpr(), gasprice.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(gasprice);
		break;
	}
	case 0x3b: {//EXTCODESIZE
		StackFrame extcodesize("mu_S_" + to_string(top));
		extcodesize.z3Expr = StackFrame::c.bv_const(("Ib_szie#" + stack[top].z3Expr.to_string()).c_str(), 256);
		//extcodesize.symbolic = stack[top].symbolic;
		string right = extcodesize.z3Expr.to_string();
		//processSymExpr(right, stack[top].symbolic);
		Expr e(256, extcodesize.getExpr(), right);
		nodes.at(NodeID).addExpr(pc, e);
		stack[top] = extcodesize;
		break;
	}
	case 0x3c: {//EXTCODECOPY
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x3d: {//RETURNDATASIZE
		StackFrame returndatasize("mu_S_" + to_string(top + 1));
		returndatasize.z3Expr = *returnDataSize;
		Expr e(256, returndatasize.getExpr(), returndatasize.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(returndatasize);
		break;
	}
	case 0x3e: {//RETURNDATACOPY
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x3f: {//EXTCODEHASH(君士坦丁堡版本新增指令)
		StackFrame extcodehash("mu_S_" + to_string(top));
		string right = "Ib_codehash#" + stack[top].z3Expr.to_string();
		extcodehash.z3Expr = StackFrame::c.bv_const(right.c_str(), 256);
		//extcodehash.symbolic = stack[top].symbolic;
		//processSymExpr(right, stack[top].symbolic);
		Expr e(256, extcodehash.getExpr(), right);
		nodes.at(NodeID).addExpr(pc, e);
		stack[top] = extcodehash;
		break;
	}

	case 0x40: {//BLOCKHASH
		StackFrame IHhash("mu_S_" + to_string(top));
		IHhash.z3Expr = StackFrame::c.bv_const(("IH_p#" + stack[top].z3Expr.to_string()).c_str(), 256);
		//IHhash.symbolic = stack[top].symbolic;
		string right = IHhash.z3Expr.to_string();
		//processSymExpr(right, stack[top].symbolic);
		Expr blockhash(256, IHhash.getExpr(), right);
		nodes.at(NodeID).addExpr(pc, blockhash);
		stack[top] = IHhash;
		break;
	}
	case 0x41: {//COINBASE
		StackFrame IHc("mu_S_" + to_string(top + 1));
		IHc.z3Expr = StackFrame::c.bv_const("IHc", 256);
		Expr e(256, IHc.getExpr(), IHc.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(IHc);
		break;
	}
	case 0x42: {//TIMESTAMP
		StackFrame IHs("mu_S_" + to_string(top + 1));
		IHs.z3Expr = StackFrame::c.bv_const("IHs", 256);
		Expr e(256, IHs.getExpr(), IHs.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(IHs);
		break;
	}
	case 0x43: {//NUMBER
		StackFrame IHi("mu_S_" + to_string(top + 1));
		IHi.z3Expr = StackFrame::c.bv_const("IHi", 256);
		Expr e(256, IHi.getExpr(), IHi.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(IHi);
		break;
	}
	case 0x44: {//DIFFICULTY
		StackFrame IHd("mu_S_" + to_string(top + 1));
		IHd.z3Expr = StackFrame::c.bv_const("IHd", 256);
		Expr e(256, IHd.getExpr(), IHd.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(IHd);
		break;
	}
	case 0x45: {//GASLIMIT
		StackFrame IH_limit("mu_S_" + to_string(top + 1));
		IH_limit.z3Expr = StackFrame::c.bv_const("IH_limit", 256);
		Expr e(256, IH_limit.getExpr(), IH_limit.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(IH_limit);
		break;
	}
	case 0x46: {//CHAINID
		StackFrame chainid("mu_S_" + to_string(top + 1));
		chainid.z3Expr = StackFrame::c.bv_const("chainid", 256);
		Expr e(256, chainid.getExpr(), chainid.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(chainid);
		break;
	}
	case 0x47: {//SELFBALANCE
		StackFrame selfbalance("mu_S_" + to_string(top + 1));
		selfbalance.z3Expr = StackFrame::c.bv_const("selfbalance", 256);
		Expr e(256, selfbalance.getExpr(), selfbalance.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(selfbalance);
		break;
	}
	case 0x50: {//POP
		stack.pop_back();
		break;
	}

			 //!? memory and storage are similar to stack(store constant and temp expr name)
			 //!? when load memory or storage variable(index is the load position)
			 //!? first see whether mem/st[index] is a constant number 
			 //!? if it's a constant then load a constant,otherwise load mem/st_index
			 //!? when store memory or storage variable(index is the store position),
			 //!? mem/st[index] = stack[top].getExpr()(result can be ether mu_S_top or a constant number)
	case 0x51: {//MLOAD
		StackFrame mloadFrame;
		string start = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_decimal_string(256) : stack[top].z3Expr.to_string();
		expr memEnd = (stack[top].z3Expr + 32).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();
		string loc = start + "$" + end;
		//bool locSym = stack[top].symbolic;
		if (memory.find(loc) != memory.end()) {
			mloadFrame.z3Expr = memory.at(loc);
			//mloadFrame.symbolic = StackFrame::exprDepth.find(mloadFrame.z3Expr.to_string()) != StackFrame::exprDepth.end();
		}
		else {
			mloadFrame.z3Expr = StackFrame::c.bv_const(("mem_" + loc).c_str(), 256);
			//mloadFrame.symbolic = stack[top].symbolic;
		}
		string right;
		if (mloadFrame.z3Expr.is_numeral()) {
			right = mloadFrame.z3Expr.get_decimal_string(256);
			mloadFrame.setType(StackType::CONSTANT);
			mloadFrame.setValue(uint256_t(right));
		}
		else {
			right = "mem_" + loc;
			//processSymExpr(right, locSym);
			mloadFrame.setType(StackType::EXPR);
			mloadFrame.setName("mu_S_" + to_string(top));
		}
		stack[top] = mloadFrame;
		Expr e(256, "mu_S_" + to_string(top), right);
		nodes.at(NodeID).addExpr(pc, e);
		break;
	}
	case 0x52: {//MSTORE
		string start = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_decimal_string(256) : stack[top].z3Expr.to_string();
		expr memEnd = (stack[top].z3Expr + 32).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();
		string loc = start + "$" + end;

		//memory[] : the lack of default constructor of z3::expr
		//memory.insert(key, value) or memory.emplace(key, value) can't insert when key already exists
		auto iter = memory.find(loc);
		if (iter == memory.end())
			memory.emplace(make_pair(loc, stack[top - 1].z3Expr));
		else
			iter->second = stack[top - 1].z3Expr;
		string left = "mem_" + loc;
		//processSymExpr(left, stack[top].symbolic);

		//if (stack[top - 1].symbolic) {
		//	StackFrame::exprDepth.insert(make_pair(stack[top - 1].z3Expr.simplify().to_string(), 0));
		//}
		string right = stack[top - 1].z3Expr.is_numeral() ? stack[top - 1].z3Expr.get_decimal_string(256) : "mu_S_" + to_string(top - 1);
		//if (stack[top - 1].symbolic) {
		//	string s = stack[top - 1].z3Expr.simplify().to_string();
		//	if (StackFrame::exprDepth.find(s) == StackFrame::exprDepth.end())
		//		StackFrame::exprDepth.insert(make_pair(s, 0));
		//}
		Expr e(256, left, right);
		nodes.at(NodeID).addExpr(pc, e);
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x53: {//MSTORE8
		string start = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_decimal_string(256) : stack[top].z3Expr.to_string();
		expr memEnd = (stack[top].z3Expr + 8).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();

		string loc = start + "$" + end;

		auto iter = memory.find(loc);
		expr storeExpr = (stack[top - 1].z3Expr & StackFrame::c.bv_val(0xff, 256)).simplify();
		if (iter == memory.end())
			memory.emplace(make_pair(loc, storeExpr));
		else {
			iter->second = storeExpr;
		}

		string left = "mem_" + loc;
		//processSymExpr(left, stack[top].symbolic);
		if (storeExpr.is_numeral())
			nodes.at(NodeID).addExpr(pc, Expr(8, left, storeExpr.get_decimal_string(256)));
		else
			nodes.at(NodeID).addExpr(pc, Expr(512, left, stack[top - 1].getExpr(), "trunc", "8"));
		//if (stack[top - 1].symbolic) {
		//	string s = storeExpr.simplify().to_string();
		//	if (StackFrame::exprDepth.find(s) == StackFrame::exprDepth.end())
		//		StackFrame::exprDepth.insert(make_pair(s, 0));
		//}
		stack.pop_back();
		stack.pop_back();
		break;
	}
			 //! Currently SLOAD and SSTORE assume location is concrete
			 //! So SSTORE need add expr st_loc = expr
			 //x eg:	st[s3] = s2 (SSTORE) can't be removed
			 //! 		s2 = 0x00	 (PUSH 0x00)
			 //!        s3 = s3      (PUSH s3)
			 //!        s3 = st[s3] (SLOAD)
			 //! 此时若仅仅在storage存储(s3,s2)
	case 0x54: {//SLOAD
		StackFrame sloadFrame;
		string loc = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_decimal_string(256) : stack[top].z3Expr.to_string();
		//bool locSym = stack[top].symbolic;
		if (storage.find(loc) != storage.end()) {
			sloadFrame.z3Expr = storage.at(loc);
			//sloadFrame.symbolic = StackFrame::exprDepth.find(sloadFrame.z3Expr.to_string()) != StackFrame::exprDepth.end();
		}
		else {
			sloadFrame.z3Expr = StackFrame::c.bv_const(("st_" + loc).c_str(), 256);
			//sloadFrame.symbolic = stack[top].symbolic;
		}
		string right;
		if (sloadFrame.z3Expr.is_numeral()) {
			right = sloadFrame.z3Expr.get_decimal_string(256);
			sloadFrame.setType(StackType::CONSTANT);
			sloadFrame.setValue(uint256_t(right));

			speSload[CFGLoc(NodeID, pc)] = right;
			//storageInstrs[right].insert(CFGLoc(NodeID, pc));
		}
		else {
			right = "st_" + loc;
			//processSymExpr(right, locSym);
			sloadFrame.setType(StackType::EXPR);
			sloadFrame.setName("mu_S_" + to_string(top));
			if (right.find(symbolicPrefix) == string::npos)
				storageInstrs[right].insert(CFGLoc(NodeID, pc));
		}
		stack[top] = sloadFrame;
		Expr e(256, "mu_S_" + to_string(top), right);

		nodes.at(NodeID).addExpr(pc, e);
		break;
	}
	case 0x55: {//SSTORE
		string loc = stack[top].z3Expr.is_numeral() ? stack[top].z3Expr.get_decimal_string(256) : stack[top].z3Expr.to_string();
		auto iter = storage.find(loc);
		if (iter == storage.end())
			storage.emplace(make_pair(loc, stack[top - 1].z3Expr));
		else
			iter->second = stack[top - 1].z3Expr;
		string left = "st_" + loc;
		//processSymExpr(left, stack[top].symbolic);
		string right = stack[top - 1].z3Expr.is_numeral() ? stack[top - 1].z3Expr.get_decimal_string(256) : "mu_S_" + to_string(top - 1);
		//if (stack[top - 1].symbolic) {
		//	string s = stack[top - 1].z3Expr.simplify().to_string();
		//	if (StackFrame::exprDepth.find(s) == StackFrame::exprDepth.end())
		//		StackFrame::exprDepth.insert(make_pair(s, 0));
		//}

		if (left.find(symbolicPrefix) == string::npos)
			storageInstrs[left].insert(CFGLoc(NodeID, pc));
		else
			SSTOREsymInstrs.insert(pc);
		Expr e(256, left, right);
		nodes.at(NodeID).addExpr(pc, e);
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x56: {//JUMP
		stack.pop_back();
		break;
	}
	case 0x57: {//JUMPI
		nodes.at(NodeID).setEndTop(int(top) - 1);
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x58: {//PC
		StackFrame plus(pc);
		plus.z3Expr = StackFrame::c.bv_val(pc, 256);

		Expr PC(256, "mu_S_" + to_string(top + 1), to_string(pc));
		nodes.at(NodeID).addExpr(pc, PC);
		stack.push_back(plus);
		break;
	}
	case 0x59: {//MSIZE
		static int msizeCnt = 0;
		StackFrame plus("mu_S_" + to_string(top + 1));
		string name = "mu_i_" + to_string(msizeCnt);
		plus.z3Expr = StackFrame::c.bv_const(name.c_str(), 256);

		Expr msize(256, plus.getExpr(), plus.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, msize);
		stack.push_back(plus);
		msizeCnt++;
		break;
	}
	case 0x5a: {//GAS
		static int gasCnt = 0;
		StackFrame plus("mu_S_" + to_string(top + 1));
		string name = "mu_g" + to_string(gasCnt);
		plus.z3Expr = StackFrame::c.bv_const(name.c_str(), 256);

		Expr gas(256, plus.getExpr(), plus.z3Expr.to_string());
		nodes.at(NodeID).addExpr(pc, gas);
		stack.push_back(plus);
		break;
	}
	case 0x5b: {//JUMPDEST
		break;
	}

	case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
	case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
		//PUSHx
		//string value = instrParts[1];
		StackFrame push;
		string right;
		if (Contract::isHex(instrParts[1].substr(2))) {
			uint256_t pushValue(instrParts[1]);
			push.setType(StackType::CONSTANT);
			push.setValue(pushValue);
			string value = boost::lexical_cast<string>(pushValue);
			push.z3Expr = StackFrame::c.bv_val(value.c_str(), 256);
			right = value;
		}
		else {//PUSH20 0x__$a8e7faaf74260e17257bd0c7c0f0ee1665$__
			static map<string, int> libAddrMap;
			static int libNum = 0;
			auto iter = libAddrMap.find(instrParts[1]);
			push.setType(StackType::EXPR);
			push.setName("mu_S_" + to_string(top + 1));
			if (iter == libAddrMap.end()) {
				libAddrMap.insert(pair<string, int>(instrParts[1], libNum));
				push.z3Expr = StackFrame::c.bv_const(("lib_" + to_string(libNum)).c_str(), 256);
				libNum++;
			}
			else
				push.z3Expr = StackFrame::c.bv_const(("lib_" + to_string(iter->second)).c_str(), 256);
			right = push.z3Expr.to_string();
		}

		Expr e(256, "mu_S_" + to_string(top + 1), right);
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(push);
		break;
	}
	case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
		//DUPx
		size_t dupLoc = top - (opcode - 0x80);
		StackFrame dupItem = stack[dupLoc];
		if (stack[dupLoc].getType() == StackType::EXPR)
			dupItem.setName("mu_S_" + to_string(top + 1));
		Expr e(256, "mu_S_" + to_string(top + 1), stack[dupLoc].getExpr());
		nodes.at(NodeID).addExpr(pc, e);
		stack.push_back(dupItem);
		break;
	}
	case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
		//SWAPx
		size_t swapLoc = top - (opcode - 0x90 + 1);
		/*StackFrame s0 = stack[0];*/ string symS0 = "mu_S_" + to_string(top);
		/*StackFrame sLoc = stack[swapLoc]; */string symSLoc = "mu_S_" + to_string(swapLoc);
		assert(stack[top].getType() != StackType::NODEF && stack[swapLoc].getType() != StackType::NODEF);
		z3::expr temp = stack[top].z3Expr;
		stack[top].z3Expr = stack[swapLoc].z3Expr;
		stack[swapLoc].z3Expr = temp;
		//bool swapSym = stack[top].symbolic;
		//stack[top].symbolic = stack[swapLoc].symbolic;
		//stack[swapLoc].symbolic = swapSym;

		if (stack[top].getType() == StackType::CONSTANT && stack[swapLoc].getType() == StackType::CONSTANT) {
			int256_t temp = stack[top].getValue();
			stack[top].setValue(stack[swapLoc].getValue());
			stack[swapLoc].setValue(temp);
			nodes.at(NodeID).addExpr(pc, Expr(256, symS0, boost::lexical_cast<string>(stack[top].getValue())));
			nodes.at(NodeID).addExpr(pc, Expr(256, symSLoc, boost::lexical_cast<string>(stack[swapLoc].getValue())));
		}
		else if (stack[swapLoc].getType() == StackType::EXPR && stack[top].getType() == StackType::CONSTANT) {
			int256_t constant = stack[top].getValue();
			stack[swapLoc].setType(StackType::CONSTANT);
			stack[swapLoc].setValue(constant);
			stack[top].setType(StackType::EXPR);
			stack[top].setName(symS0);

			nodes.at(NodeID).addExpr(pc, Expr(256, symS0, symSLoc));
			nodes.at(NodeID).addExpr(pc, Expr(256, symSLoc, boost::lexical_cast<string>(constant)));
		}
		else if (stack[swapLoc].getType() == StackType::CONSTANT && stack[0].getType() == StackType::EXPR) {
			int256_t constant = stack[swapLoc].getValue();
			stack[top].setType(StackType::CONSTANT);
			stack[top].setValue(constant);
			stack[swapLoc].setType(StackType::EXPR);
			stack[swapLoc].setName(symSLoc);

			nodes.at(NodeID).addExpr(pc, Expr(256, symSLoc, symS0));
			nodes.at(NodeID).addExpr(pc, Expr(256, symS0, boost::lexical_cast<string>(constant)));
		}
		else if (stack[swapLoc].getType() == StackType::EXPR && stack[0].getType() == StackType::EXPR) {
			//! stack expr not change, only need to add expr
			string temp1 = "temp256_" + to_string(Operand::getNum256());
			//!? temp256_num256'1 = mu_S_0
			//!? mu_S_0 = mu_S_sLoc
			//!? mu_S_sLoc = temp256_num256'1
			nodes.at(NodeID).addExpr(pc, Expr(256, temp1, symS0));
			nodes.at(NodeID).addExpr(pc, Expr(256, symS0, symSLoc));
			nodes.at(NodeID).addExpr(pc, Expr(256, symSLoc, temp1));
		}
		break;
	}
	case 0xa0:case 0xa1:case 0xa2:case 0xa3:case 0xa4: {//LOGx
		int num = opcode - 0xa0 + 2;
		for (int i = 0; i < num; i++)
			stack.pop_back();
		break;
	}

	case 0xf0: {//CREATE
		expr outSize = StackFrame::c.bv_const(0, 256);
		if (returnDataSize == NULL)
			returnDataSize = new expr(outSize);
		else {
			//cout << "returnDataSize : " << (*returnDataSize) << endl;
			delete returnDataSize;
			returnDataSize = new expr(outSize);
		}

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame create("mu_S_" + to_string(top + 1));
		create.z3Expr = StackFrame::c.bv_const(("create" + to_string(createNum)).c_str(), 256);
		stack.push_back(create);
		createNum++;
		break;
	}
	case 0xf1: {//CALL
		//operand order : gas, to, value, in offset, in size, out offset, out size
		processReturnData(stack[top - 5].z3Expr, stack[top - 6].z3Expr, memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame call("mu_S_" + to_string(top + 1));
		call.z3Expr = StackFrame::c.bool_const(("call" + to_string(callNum)).c_str());
		stack.push_back(call);
		callNum++;
		break;
	}
	case 0xf2: {//CALLCODE
		//operand order : gas, to, value, in offset, in size, out offset, out size
		//use caller's storage
		processReturnData(stack[top - 5].z3Expr, stack[top - 6].z3Expr, memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame callcode("mu_S_" + to_string(top + 1));
		callcode.z3Expr = StackFrame::c.bool_const(("call" + to_string(callNum)).c_str());
		stack.push_back(callcode);
		callNum++;
		break;
	}
	case 0xf3: {//RETURN
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0xf4: {//DELEGATECALL
		//operand order : gas, to, in offset, in size, out offset, out size
		processReturnData(stack[top - 4].z3Expr, stack[top - 5].z3Expr, memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame delegatecall("mu_S_" + to_string(top + 1));
		delegatecall.z3Expr = StackFrame::c.bool_const(("call" + to_string(callNum)).c_str());
		stack.push_back(delegatecall);
		callNum++;
		break;
	}
	case 0xf5: {//CREATE2
		expr outSize = StackFrame::c.bv_const(0, 256);
		if (returnDataSize == NULL)
			returnDataSize = new expr(outSize);
		else {
			//cout << "returnDataSize : " << (*returnDataSize) << endl;
			delete returnDataSize;
			returnDataSize = new expr(outSize);
		}

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame create2("mu_S_" + to_string(top + 1));
		create2.z3Expr = StackFrame::c.bv_const(("create" + to_string(createNum)).c_str(), 256);
		stack.push_back(create2);
		createNum++;
		break;
	}
	case 0xfa: {//STATICCALL
		//operand order : gas, to, in offset, in size, out offset, out size
		processReturnData(stack[top - 4].z3Expr, stack[top - 5].z3Expr, memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		StackFrame staticcall("mu_S_" + to_string(top + 1));
		staticcall.z3Expr = StackFrame::c.bool_const(("call" + to_string(callNum)).c_str());
		stack.push_back(staticcall);
		callNum++;
		break;
	}
	case 0xfd: {//REVERT
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0xfe: {//INVALID
		//cout << "INVALID" << endl;
		break;
	}
	case 0xff: {//SELFDESTRUCT
		stack.pop_back();
		break;
	}
	default:
		cerr << "Wrong opcode 0x" << std::hex << opcode << endl;
		break;
	}

	int afterStackSize = static_cast<int>(stack.size());
	assert(afterStackSize - beforeStackSize == get<1>(Opcode::getOperation(opcode)) - get<0>(Opcode::getOperation(opcode)));

	bool debug = false;
	if (debug) {
		displayRedMsg(to_string(pc) + " : " + instr + " stack top No : " + to_string(afterStackSize - 1));
		auto& exprs = nodes.at(NodeID).getExprs();
		if (exprs.find(pc) != exprs.end()) {
			for (auto& e : exprs.at(pc)) {
				string exprString = e.getExprString();
				if (exprString.find("symbolic_stack_") != string::npos)
					displayYellowMsg(exprString);
				else
					cout << exprString << endl;
			}
		}
		displayStackFrame(stack);
	}
}

string genSymStackItemName(int NodeID, int depth) {
	return symbolicPrefix + "$" + to_string(NodeID) + "_" + to_string(depth);
}

void mergeInstrState(int curID, InstrState* src, z3::context& c, vector<z3::expr>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage) {
	for (size_t i = 0; i < stack.size(); i++)
		if (stack[i].simplify().to_string() != src->stack[i].simplify().to_string())
			src->stack[i] = c.bv_const(genSymStackItemName(curID, (int)i).c_str(), 256);
	for (auto& m : memory)
		if (src->memory.find(m.first) != src->memory.end() && m.second.simplify().to_string() != src->memory.at(m.first).simplify().to_string())
			src->memory.erase(m.first);

	vector<string> toBeErased;
	for (auto& m : src->memory)
		if (memory.find(m.first) == memory.end())
			toBeErased.push_back(m.first);
	for (auto& str : toBeErased)
		src->memory.erase(str);


	for (auto& s : storage)
		if (src->storage.find(s.first) != src->storage.end() && s.second.simplify().to_string() != src->storage.at(s.first).simplify().to_string())
			src->storage.erase(s.first);

	toBeErased.clear();
	for (auto& s : src->storage)
		if (storage.find(s.first) == storage.end())
			toBeErased.push_back(s.first);
	for (auto& str : toBeErased)
		src->storage.erase(str);
}

void symExecNode(int NodeID, int targetID, int idom, const map<int, ECFGNode>& runtimeNodes, map<int, set<int>>& partEdges, z3::context& c, vector<z3::expr>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, InstrState* afterTargetStates) {
	static bool exists = false;
	auto node = runtimeNodes.at(NodeID);
	if (NodeID == targetID) {
		if (!exists) {
			afterTargetStates->stack = stack;
			afterTargetStates->memory = memory;
			afterTargetStates->storage = storage;
			exists = true;
		}
		else
			mergeInstrState(targetID, afterTargetStates, c, stack, memory, storage);
		return;
	}

	if (NodeID != idom) {
		for (auto& instr : node.getInstrs()) {
			z3::expr jumpiCond = c.bool_val(true);
			symExecInstr(instr.first, instr.second, c, stack, memory, storage, jumpiCond);
			bool debug = false;
			if (debug) {
				displayGreenMsg("NodeID_" + to_string(NodeID) + " : " + to_string(instr.first) + " " + instr.second);
				for (size_t i = 0; i < stack.size(); i++)
					cout << i << " " << stack[i].to_string() << endl;
			}
		}
	}
	else
		//标志着开始新节点的遍历
		exists = false;

	if (partEdges.at(NodeID).size() > 1) {
		assert(partEdges.at(NodeID).size() == 2);
		auto iter = partEdges.at(NodeID).begin();
		int firstChd = *iter;
		iter++;
		int secChd = *iter;
		vector<expr> dupStack = stack;
		map<string, expr> dupMem = memory;
		map<string, expr> dupStorage = storage;
		symExecNode(firstChd, targetID, idom, runtimeNodes, partEdges, c, stack, memory, storage, afterTargetStates);
		symExecNode(secChd, targetID, idom, runtimeNodes, partEdges, c, dupStack, dupMem, dupStorage, afterTargetStates);
	}
	else if (partEdges.at(NodeID).size() == 1) {
		int chd = *partEdges.at(NodeID).begin();
		symExecNode(chd, targetID, idom, runtimeNodes, partEdges, c, stack, memory, storage, afterTargetStates);
	}
}

void genDomTreeDotFile(string fileName, const map<int, set<int>>& domtree, const set<int>& loopHeader) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : domtree) {
		string blockName = "Node_" + to_string(n.first);
		string color;
		if (loopHeader.find(n.first) != loopHeader.end())
			color += ", color = blue";
		string nodeLabel = "[label = \"" + blockName + "\"" + color + "]";
		//string nodeLabel = "";
		dotFile += blockName + nodeLabel + "\r\n";
		for (auto &c : n.second) {
			string chdName = "Node_" + to_string(c);
			dotFile += "\t" + blockName + " -> " + chdName + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();

}
void genDomTreeDotFile(string fileName, const map<int, set<int>>& domTree) {
	genDomTreeDotFile(fileName, domTree, { });
}
void genDomSet(int curID, const map<int, set<int>>& domTree, map<int, set<int>>& domSet) {
	domSet[curID] = { curID };
	for (auto& c : domTree.at(curID)) {
		genDomSet(c, domTree, domSet);
		const set<int>& chdSet = domSet.at(c);
		domSet.at(curID).insert(chdSet.begin(), chdSet.end());
	}
}
void genDomSet(const map<int, set<int>>& domTree, map<int, set<int>>& domSet) {
	genDomSet(0, domTree, domSet);
}

void getLoopHeader(const map<int, set<int>>& reEdges, const map<int, set<int>>&domTree, set<int>& loopHeader) {
	map<int, set<int>> domSet;
	genDomSet(domTree, domSet);
	for (auto& n : reEdges)
		for (auto& p : n.second) {
			if (domSet.at(n.first).find(p) != domSet.at(n.first).end())
				loopHeader.insert(n.first);
			if (p == n.first)//自环，一般出现在string相关的计算过程中
				loopHeader.insert(n.first);
		}
}
//IDom(n)不可能为n
//判断从start到end之间的路径是否存在环，其中start为end的支配节点(不一定是直接支配节点)
bool loopExists(int start, int end, const map<int, set<int>>& reEdges) {
	if (start == end)
		if (reEdges.at(start).find(end) != reEdges.at(start).end())
			return true;
		else
			return false;
	map<int, int> visitState;
	vector<int> stack;
	stack.push_back(end);
	visitState[end] = 1;
	while (!stack.empty()) {
		int top = stack.back();

		bool flag = true;
		for (auto chd : reEdges.at(top))
			if (chd == start)
				continue;
			else if (visitState.find(chd) == visitState.end()) {
				stack.push_back(chd);
				visitState[chd] = 1;
				flag = false;
				break;
			}
			else if (visitState.at(chd) == 1)
				return true;
			else
				continue;

		if (flag) {
			visitState[top] = 2;
			stack.pop_back();
		}
	}

	return false;

}

void genIdomLoopRelNode(const map<int, int>& idom, const map<int, set<int>>& reEdges, set<int>& retNodes) {
	for (auto& i : idom) {
		if (i.second == -1)
			continue;
		if (loopExists(i.second, i.first, reEdges))
			retNodes.insert(i.first);
	}
}

set<int> genIndependentBlocks(const map<int, EBasicBlock>& blocks) {
	set<int> independentBlocks;
	for (auto& bb : blocks) {
		bool flag = true;
		for (auto& instr : bb.second.getInstrs())
			if (instr.second.find("PUSH") != string::npos || instr.second.find("DUP") != string::npos || instr.second.find("SWAP") != string::npos
				|| instr.second == "POP" || instr.second == "JUMP" || instr.second == "JUMPDEST")
				continue;
			else {
				flag = false;
				break;
			}
		if (flag)
			independentBlocks.insert(bb.first);
	}
	return independentBlocks;
}

bool dominates(int id1, int id2, const map<int, int>& IDom) {
	if (id1 == id2)
		return true;
	int up = id2;
	while (IDom.at(up) != -1) {
		up = IDom.at(up);
		if (up == id1)
			return true;
	}
	return false;
}

//对有向无环图进行拓扑排序
void topSort(const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& domTree, const map<int, int>& IDom, const set<int>& idomLoopRelNodes, vector<int>& order, const set<int>& independentBlocks) {
	map<int, set<int>> dag = domTree;

	//这里是为了正确生成第3类节点（节点类型查看函数调用处的说明）的拓扑排序
	for (auto& n : idomLoopRelNodes)
		for (auto pnt : runtimeNodes.at(n).getParents())
			if (pnt == -1)
				continue;
			else
				dag.at(pnt).insert(n);
	
	//经过部分测试用例测试发现，终止块由于其父节点个数较多，如果该终止块为1类节点，可能导致生成的partEdges过于庞大，致使生成约束的时间过慢
	//目前为了方便处理（至少用在检测冗余SLOAD的约束生成可以如此处理，因为终止块一般不会出现冗余SLOAD的情况。后续验证模块应该如何处理再考虑），所有终止块也采用第三类节点的生成方式
	//同理为了方便处理 所有independentBLock生成的Node也均采用第三类节点的生成方式
	for(auto& node : runtimeNodes)
		if(node.second.getBlockType() == BlockType::REVERT || node.second.getBlockType() == BlockType::INVALID || node.second.getBlockType() == BlockType::RETURN || node.second.getBlockType() == BlockType::STOP || node.second.getBlockType() == BlockType::SELFDESTRUCT
			|| independentBlocks.find(node.second.getStart()) != independentBlocks.end())
			for(auto& pnt : node.second.getParents())
				if (pnt == -1)
					continue;
				else if(!dominates(node.first, pnt, IDom))//防止形成环，该限制条件一般限制的为loopHeader，所以不需要在引用该函数的symExecNodes函数中进行节点再分类
					dag.at(pnt).insert(node.first);

	//genDomTreeDotFile("domTree.dot", dag);

	map<int, int> inDegree;
	for (auto& n : dag)
		for (auto& chd : n.second)
			inDegree[chd]++;
	queue<int> que;
	que.push(0);
	while (!que.empty()) {
		int front = que.front();
		que.pop();
		order.push_back(front);
		for (auto& chd : dag.at(front)) {
			inDegree[chd]--;
			if (inDegree.at(chd) == 0) {
				que.push(chd);
				inDegree.erase(chd);
			}
		}
	}

	assert(inDegree.empty());
}

//void genTraverseOrder(int curID, const map<int, set<int>>& domTree, set<int>& idomLoopRelNodes, vector<int>& order) {
//	map<int, vector<int>> secOrders;
//	queue<int> que;
//	que.push(curID);
//	while (!que.empty()) {
//		int front = que.front();
//		que.pop();
//		order.push_back(front);
//		for(auto& chd : domTree.at(front))
//			if (idomLoopRelNodes.find(chd) != idomLoopRelNodes.end()) {
//				secOrders[chd] = { };
//				genTraverseOrder(chd, domTree, idomLoopRelNodes, secOrders.at(chd));
//			}
//			else
//				que.push(chd);
//	}
//	for(auto& odr : secOrders)
//		order.insert(order.end(), odr.second.begin(), odr.second.end());
//}

void Contract::symExecNodes(map<int, ECFGNode>& runtimeNodes, const map<int, EBasicBlock>& blocks) {
	map<int, set<int>> edges;
	map<int, set<int>> reEdges;
	set<int> allNodes;
	for (auto& i : runtimeNodes) {
		edges[i.first] = { };
		reEdges[i.first] = { };
		allNodes.insert(i.first);
		if (i.second.getJumpID() != -1)
			edges.at(i.first).insert(i.second.getJumpID());
		if (i.second.getFallsID() != -1)
			edges.at(i.first).insert(i.second.getFallsID());
		for (auto& pnt : i.second.getParents())
			if (pnt != -1)
				reEdges.at(i.first).insert(pnt);
	}

	map<int, set<int>> scc;
	calScc(edges, scc);

	//for (auto& s : scc) {
	//	for (auto& other : s.second)
	//		cout << other << " ";
	//	cout << endl;
	//}

	set<int> loopRelNodes;
	genLoopRelNodes(edges, scc, loopRelNodes);

	//cout << "Loop Related Nodes : ";
	//for (auto& n : loopRelNodes)
	//	cout << n << " ";
	//cout << endl;

	set<int> nonloopRelNodes;
	std::set_difference(allNodes.begin(), allNodes.end(), loopRelNodes.begin(), loopRelNodes.end(), inserter(nonloopRelNodes, nonloopRelNodes.end()));

	map<int, int> beforeStackDepth;
	for (auto& i : stack2NodeID)
		beforeStackDepth.insert(make_pair(i.second, int(i.first.size()) - 1));

	map<int, int> IDom = genIDom(edges);
	map<int, set<int>> domTree;
	::genDomTree(IDom, domTree);

	set<int> loopHeader;
	getLoopHeader(reEdges, domTree, loopHeader);

	string name = this->name;
	name[name.find_last_of(':')] = '.';
	//genDomTreeDotFile(name + ".domTree.dot", domTree);
	genDomTreeDotFile(name + ".domTree.dot", domTree, loopHeader);

	//存储的是从Idom(n)节点开始到n节点的所有路径符号执行到达n节点（未执行n节点的指令）时的状态
	map<int, InstrState*> beforeNodeStates;
	
	//存储的是从Idom(n)节点开始到n节点的所有路径符号执行到达并执行了n节点指令时的状态
	map<int, InstrState*> afterNodeStates;


	//对于nonloop相关的节点id，先是通过构造所有的以其直接支配节点idom(id)为起始，以节点id为终止的CFG中的子图
	//然后从idom(id)节点开始进行符号执行

	//loop相关的节点从根本上就不能使用不同路径遍历取相同部分的做法
	//因为路径是无穷的
	
	//node分为若干类型
	//1.与循环体无关，这样可以尽可能生成约束(当然CFG的起始节点0需要单独处理)
	//2.循环体头部，从完全符号化的自由变量开始生成
	//3.非循环体头部，且其支配节点到自身的路径中还存在循环体（即路径是不可穷尽的）,此类节点可以放在处理队列末尾等候下一次处理
	//4.非循环体头部，且其支配节点到自身的路径是可穷尽的
	set<int> idomLoopRelNodes;
	genIdomLoopRelNode(IDom, reEdges, idomLoopRelNodes);
	for (auto& lh : loopHeader)
		idomLoopRelNodes.erase(lh);
	vector<int> traverseOrder;

	set<int> independentBlocks = genIndependentBlocks(blocks);
	//set<int> exceptionBlocks;

	topSort(runtimeNodes, domTree, IDom, idomLoopRelNodes, traverseOrder, independentBlocks);
	//genTraverseOrder(0, domTree, idomLoopRelNodes, traverseOrder);
	for (auto& id : traverseOrder) {
		InstrState* state = new InstrState();
		const ECFGNode& curNode = runtimeNodes.at(id);
		int instrStart = curNode.getStart();
		int instrEnd = curNode.getEnd();
		//displayGreenMsg("Node_" + to_string(id) + " : " + to_string(instrStart) + "$" + to_string(instrEnd));

		vector<StackFrame> stackframe;
		map<string, z3::expr> mem;
		map<string, z3::expr> st;


		if (loopHeader.find(id) != loopHeader.end()) {//2类节点
			int depth = beforeStackDepth.at(id);
			for (int i = 0; i < depth; i++) {
				state->stack.push_back(StackFrame::c.bv_const(genSymStackItemName(id, i).c_str(), 256));
			}
		}
		else if (idomLoopRelNodes.find(id) != idomLoopRelNodes.end() || 
			(curNode.getBlockType() == BlockType::REVERT || curNode.getBlockType() == BlockType::INVALID || curNode.getBlockType() == BlockType::RETURN || curNode.getBlockType() == BlockType::STOP || curNode.getBlockType() == BlockType::SELFDESTRUCT)
			|| independentBlocks.find(curNode.getStart()) != independentBlocks.end()) {//3类节点
			//assert(idomLoopRelNodes.find(id) == idomLoopRelNodes.end() || reEdges.at(id).size() > 1);
			bool flag = false;
			for(auto& pnt : reEdges.at(id))
				if (!flag) {
					state->stack = afterNodeStates.at(pnt)->stack;
					state->memory = afterNodeStates.at(pnt)->memory;
					state->storage = afterNodeStates.at(pnt)->storage;
					flag = true;
				}
				else
					mergeInstrState(id, state, StackFrame::c, afterNodeStates.at(pnt)->stack, afterNodeStates.at(pnt)->memory, afterNodeStates.at(pnt)->storage);
		}
		else if (id != 0) {//1,4类节点
			map<int, set<int>> partEdges;
			genPartEdges(reEdges, IDom.at(id), id, partEdges);
			const InstrState* s = afterNodeStates.at(IDom.at(id));
			vector<z3::expr> stack = s->stack;
			map<string, z3::expr> memory = s->memory;
			map<string, z3::expr> storage = s->storage;
			int start = IDom.at(id);
			int idom = start;
			::symExecNode(start, id, idom, runtimeNodes, partEdges, StackFrame::c, stack, memory, storage, state);
		}


		beforeNodeStates.insert(make_pair(id, state));

		for (size_t i = 0; i < state->stack.size(); i++) {
			stackframe.push_back(StackFrame());
			if (state->stack[i].is_numeral()) {
				stackframe[i].setType(StackType::CONSTANT);
				stackframe[i].setValue(int256_t(state->stack[i].get_decimal_string(256)));
				//stackframe[i].symbolic = false;
			}
			else {
				stackframe[i].setType(StackType::EXPR);
				stackframe[i].setName("mu_S_" + to_string(i));
				//if (state->stack[i].to_string().find(symbolicPrefix) != string::npos)
				//	stackframe[i].symbolic = true;
				//else
				//	stackframe[i].symbolic = false;
			}
			stackframe[i].z3Expr = state->stack[i];
		}
		mem = state->memory;
		st = state->storage;

		//if (id != 0) {
		//	string idomInfo = "Node " + to_string(id) + "'s before Stack";
		//	displayYellowMsg(idomInfo);
		//	displayStackFrame(stackframe);
		//}
		for (auto& instr : runtimeNodes.at(id).getInstrs())
			symExecInstr(id, instr.first, instr.second, stackframe, mem, st, runtimeNodes);
		InstrState* afterState = new InstrState();
		for (auto& s : stackframe)
			afterState->stack.push_back(s.z3Expr);
		afterState->memory = mem;
		afterState->storage = st;
		afterNodeStates.insert(make_pair(id, afterState));
	}
	for (auto& b : beforeNodeStates)
		delete b.second;
	for (auto& a : afterNodeStates)
		delete a.second;
}

void Contract::testSymStack(map<int, ECFGNode>& runtimeNodes) {
	map<int, int> beforeStackDepth;
	for (auto& i : stack2NodeID)
		beforeStackDepth.insert(make_pair(i.second, int(i.first.size()) - 1));
	for (auto& i : runtimeNodes) {
		//for (auto& depth : StackFrame::exprDepth) {
		//	depth.second++;
		//}
		int instrStart = runtimeNodes.at(i.first).getStart();
		int instrEnd = runtimeNodes.at(i.first).getEnd();
		displayPurpleMsg("Node_" + to_string(i.first) + " : " + to_string(instrStart) + "$" + to_string(instrEnd));
		vector<StackFrame> stack;
		int depth = beforeStackDepth.at(i.first);
		for (int d = 0; d < depth; d++) {
			stack.push_back(StackFrame());
			stack[d].setType(StackType::EXPR);
			stack[d].setName("mu_S_" + to_string(d));
			stack[d].z3Expr = StackFrame::c.bv_const(genSymStackItemName(i.first, d).c_str(), 256);
			//stack[d].symbolic = true;
		}
		map<string, z3::expr> memory;
		map<string, z3::expr> storage;
		for (auto& instr : i.second.getInstrs()) {
			symExecInstr(i.first, instr.first, instr.second, stack, memory, storage, runtimeNodes);
		}
	}
}

void Contract::reWriteExpr(map<int, ECFGNode>& nodes) {
	//Step 1: calculate dominance frontier
	map<int, set<int>> graph;//NodeID => child node set
	map<int, set<int>> parents;//NodeID => parent node set

	//1.1 initialize graph and parents
	for (auto& node : nodes) {
		// graph[NodeID] and parents[NodeID] need to be intialized to a empty set
		//otherwise graph will not contain leaf node, and parents will not contain root node
		graph[node.first] = {};
		parents[node.first] = {};
		if (node.second.getJumpID() != -1)
			graph[node.first].insert(node.second.getJumpID());
		if (node.second.getFallsID() != -1)
			graph[node.first].insert(node.second.getFallsID());
		for (auto& i : node.second.getParents())
			if (i != -1)
				parents[node.first].insert(i);
	}

	map<int, int> IDom = genIDom(graph);
	map<int, set<int>> dTree;
	::genDomTree(IDom, dTree);

	//1.2 calculate dominance frontier
	map<int, set<int>>DF;
	for (auto& g : graph)
		DF[g.first] = {};
	for (auto& g : graph) {
		if (parents.at(g.first).size() > 1)//start node's parents is -1,size == 1
			for (auto& pre : parents.at(g.first)) {
				int runner = pre;
				while (runner != IDom.at(g.first) && runner != -1) {
					DF[runner].insert(g.first);
					runner = IDom.at(runner);
				}
			}
	}

	//Step 2: insert phi function
	set<string> Globals;
	set<string> globalNames;
	map<string, set<int>> Blocks;
	for (auto& g : graph) {
		set<string> varkill;
		//cout << "Node_" << g.first << endl;
		for (auto& exprs : nodes.at(g.first).getExprs()) {
			//cout << "\tinstr addr : " << exprs.first<<endl;
			for (auto& expr : exprs.second) {
				//cout << "\t\t" << expr.getExprString() << endl;
				for (int i = 0; i < expr.getRightNum(); i++) {
					string rv = expr.getRightName(i);
					if (!isNumerical(rv))
						globalNames.insert(rv);
					if (varkill.find(rv) == varkill.end() && !isNumerical(rv))
						Globals.insert(rv);
				}
				string lv = expr.getLeftName();
				globalNames.insert(lv);
				if (expr.getLopStr() == "=") {//! currently only assign operator kills the operand 
					varkill.insert(lv);
					//Blocks(variable) contains all the block IDs which defines the variable
					//That is to say, Blocks(variable) contains operation : "variable = v1 op v2"
					Blocks[lv].insert(g.first);
				}
			}
		}
	}
	for (set<string>::iterator iter = Globals.begin(); iter != Globals.end(); iter++) {
		vector<int> WorkList;
		for (auto& b : Blocks[*iter])
			WorkList.push_back(b);
		map<int, bool> added;
		for (auto& g : graph)
			added[g.first] = false;
		while (!WorkList.empty()) {
			int b = WorkList.back();
			WorkList.pop_back();
			if (added[b])//phi function related to b has been added to b's dominance frontier
				continue;
			for (auto d : DF[b])
				if (!nodes.at(d).hasPhiFunc(*iter)) {
					nodes.at(d).insertPhiFunc(*iter);//!? critical phi function insertion
					//Note that vector has no member function "find"
					if (find(WorkList.begin(), WorkList.end(), d) == WorkList.end())
						WorkList.push_back(d);
				}
			added[b] = true;
		}
	}

	//Step 3: rewrite expression
	map<string, int>counter;//variable name => counter
	map<string, vector<int>> stack;//variable name => current counter used
	for (auto v : globalNames) {
		counter.insert(pair<string, int>(v, 1));
		stack.insert(pair<string, vector<int>>(v, { 0 }));
	}
	rename(nodes.begin()->first, graph, nodes, counter, stack, IDom, dTree);

	//insert phi related assignment at the end of each block
	for (auto& node : nodes) {
		for (auto& var : node.second.getPhiFuncs()) {
			int leftIdx = node.second.getPhiLeftIdx(var);
			for (auto& idIdx : node.second.getPhiRightIdx(var)) {
				int nodeID = idIdx.first;
				int idx = idIdx.second;
				//TODO: Currently, all expr is added by default at 256 bits 
				nodes.at(nodeID).insertPhiAssign(256, var, leftIdx, idx);
			}
		}
	}
}

int Contract::NewName(const string& varName, map<string, int>& counter, map<string, vector<int>>& stack) {
	int i = counter[varName];
	counter[varName] = counter[varName] + 1;
	stack[varName].push_back(i);
	return i;
}
void Contract::rename(int NodeID, const map<int, set<int>>& graph, map<int, ECFGNode>& nodes, map<string, int>& counter, map<string, vector<int>>& stack, const map<int, int>& IDom, const map<int, set<int>>& dTree) {
	//!? generate phi function's left variable index
	for (auto var : nodes.at(NodeID).getPhiFuncs()) {//for each phi function in Node_NodeID : "var = phi(...)"
		nodes.at(NodeID).setPhiLeftIdx(var, NewName(var, counter, stack));//rewrite var as "var_NewName(var)"
	}

	//!? for each operation"x = y op z"
	//!? exprs use Operand::index, phi function use CFGNode::phiLeft and CFGNode::phiRight
	for (auto& exprs : nodes.at(NodeID).getExprs())
		for (auto& expr : exprs.second) {
			for (int i = 0; i < expr.getRightNum(); i++) {//! right operands is referenced only
				string rvalue = expr.getRightName(i);
				if (!isNumerical(rvalue))
					expr.setRightIndex(stack[rvalue].back(), i);
			}
			if (expr.getLopStr() != "=")//! currently only assign operator redefine left operand
				expr.setLeftIndex(stack[expr.getLeftName()].back());
			else
				expr.setLeftIndex(NewName(expr.getLeftName(), counter, stack));
		}
	nodes.at(NodeID).setEndTopIdx(stack[nodes.at(NodeID).getEndTopStr()].back());

	//cout << "After rename phrase" << endl;
	//cout << "Node_" << NodeID << endl;
	//for (auto& exprs : nodes.at(NodeID).getExprs()) {
	//	cout << "\tinstr addr" << exprs.first << endl;
	//	for (auto& expr : exprs.second) {
	//		cout << "\t\t";
	//		expr.print();
	//	}
	//}
	//cout << "endTop is " << nodes.at(NodeID).getEndTopStr() << "#" << nodes.at(NodeID).getEndTopIdx() << endl;
	//!? fill in phi function parameters for NodeID's successor in the CFG
	for (auto& successor : graph.at(NodeID)) {
		for (auto& phiVar : nodes.at(successor).getPhiFuncs()) {
			nodes.find(successor)->second.setPhiRightIdx(phiVar, NodeID, stack[phiVar].back());
		}
	}

	//!? for each successor s of NodeID in the dominator tree : Rename(s)
	for (auto& suc : dTree.at(NodeID))
		rename(suc, graph, nodes, counter, stack, IDom, dTree);

	for (auto& exprs : nodes.at(NodeID).getExprs())
		for (auto& expr : exprs.second) {
			if (expr.getLopStr() == "=")
				stack[expr.getLeftName()].pop_back();
		}
}

void Contract::genSSAFile(map<int, ECFGNode>& nodes, string fileName) {
	ofstream outFile(fileName);
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	for (auto& node : nodes) {
		outFile << "After rename phrase" << endl;
		outFile << "Node_" << node.first << endl;
		for (auto& exprs : node.second.getExprs()) {
			outFile << "\tinstr addr " << exprs.first << "\t" << instructions.at(exprs.first) << endl;
			for (auto& expr : exprs.second) {
				outFile << "\t\t" << expr.getExprString() << endl;
				//expr.print();
			}
		}
		for (auto& expr : node.second.getPhiAssign()) {
			outFile << "\t\t\t" << expr.getExprString() << endl;
			//expr.print();
		}
	}
	outFile.close();
}

//判断loc1.NodeID是否支配loc2.NodeID
bool dominates(const CFGLoc& loc1, const CFGLoc& loc2, const map<int, int>& IDom) {
	if (loc1.NodeID == loc2.NodeID)
		if (loc1.pc < loc2.pc)
			return true;
		else
			return false;
	int up = loc2.NodeID;
	while (IDom.at(up) != -1) {
		up = IDom.at(up);
		if (up == loc1.NodeID)
			return true;
	}
	return false;
}

//判断loc1.NodeID和loc2.NodeID之间是否有支配关系
bool dominanceWExists(const CFGLoc& loc1, const CFGLoc& loc2, const map<int, int>& IDom) {
	return dominates(loc1, loc2, IDom) || dominates(loc2, loc1, IDom);
}

void genCFGLocIDom(const map<CFGLoc, set<CFGLoc>>& domRelation, map<CFGLoc, CFGLoc>& IDom) {
	map<CFGLoc, set<CFGLoc>> reDomRel;
	for (auto& d : domRelation) {
		if (reDomRel.find(d.first) == reDomRel.end())
			reDomRel[d.first] = { };
		for (auto& c : d.second)
			reDomRel[c].insert(d.first);
	}

	for (auto& r : reDomRel) {
		if (r.second.empty()) {
			IDom.insert(make_pair(r.first, CFGLoc(0, 0)));
			continue;
		}
		auto iter = r.second.begin();
		CFGLoc candidateIDom = *iter;
		iter++;
		while (iter != r.second.end()) {
			auto candidateDomSets = domRelation.at(candidateIDom);
			if (candidateDomSets.find(*iter) != candidateDomSets.end())
				candidateIDom = *iter;
			iter++;
		}
		IDom.insert(make_pair(r.first, candidateIDom));
	}
}

void genCFGLocDomDotFile(const map<CFGLoc, CFGLoc>& IDom, const map<int, int>& maxDepths, const map<int, map<int, tuple<int, int>>>& nodeDepths, string fileName) {
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : nodeDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : IDom) {
		string callchain;
		if (nodeDepths.find(n.first.NodeID) != nodeDepths.end()) {
			assert(maxDepths.at(n.first.NodeID) == nodeDepth2FuncStart.at(n.first.NodeID).size());
			for (auto& depth : nodeDepth2FuncStart.at(n.first.NodeID))
				callchain += "-" + to_string(get<1>(depth.second)) + "(" + to_string(get<0>(depth.second)) + ")";
		}

		string blockName = "Node_" + to_string(n.first.NodeID) + "_" + to_string(n.first.pc);
		string label = to_string(n.first.NodeID) + "#" + to_string(n.first.pc) + "^" + to_string(maxDepths.at(n.first.NodeID));
		dotFile += blockName + "[label = \"" + label + callchain + "\"]\r\n";
		//if (!(n.first.NodeID == 0 && n.first.pc == 0)) {
			string idomName = "Node_" + to_string(n.second.NodeID) + "_" + to_string(n.second.pc);
			dotFile += "\t" + idomName + " -> " + blockName + ";\r\n";
		//}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}
void genCFGLocDomDotFile(const map<CFGLoc, set<CFGLoc>>& validDom, const map<int, int>& maxDepths, const map<int, map<int, tuple<int, int>>>& nodeDepths, string fileName, map<CFGLoc, map<CFGLoc, tuple<int, int>>> idomEdgeDepthChanges = {}) {
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : nodeDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : validDom) {
		string callchain;
		if (nodeDepths.find(n.first.NodeID) != nodeDepths.end()) {
			assert(maxDepths.at(n.first.NodeID) == nodeDepth2FuncStart.at(n.first.NodeID).size());
			for (auto& depth : nodeDepth2FuncStart.at(n.first.NodeID))
				callchain += "-" + to_string(get<1>(depth.second)) + "(" + to_string(get<0>(depth.second)) + ")";
		}

		string blockName = "Node_" + to_string(n.first.NodeID) + "_" + to_string(n.first.pc);
		string label = to_string(n.first.NodeID) + "#" + to_string(n.first.pc) + "^" + to_string(maxDepths.at(n.first.NodeID));
		dotFile += blockName + "[label = \"" + label + callchain + "\"]\r\n";



		for(auto& chd : n.second) {
			string chdName = "Node_" + to_string(chd.NodeID) + "_" + to_string(chd.pc);
			string content;
			if (!idomEdgeDepthChanges.empty() && n.first != CFGLoc(0, 0)) {
				tuple<int, int> t = idomEdgeDepthChanges.at(n.first).at(chd);
				content += to_string(get<0>(t)) + "_" + to_string(get<1>(t));
			}
			string label = "[label = \"" + content + "\"]";
			dotFile += "\t" + blockName + " -> " + chdName + label + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}


void genCFGLocDomDotFile(const map<CFGLoc, set<CFGLoc>>& validDom, const map<int, int>& maxDepths, const map<int, map<int, tuple<int, int>>>& nodeDepths, string fileName, const map<CFGLoc, map<CFGLoc, tuple<int, int>>>& idomEdgeDepthChanges, const map<CFGLoc, tuple<int, int>>& acIdomNodeDepthChanges, const map<CFGLoc, map<CFGLoc, tuple<int, int>>>& acIdomEdgeDepthChanges) {
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : nodeDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : validDom) {
		string callchain;
		if (nodeDepths.find(n.first.NodeID) != nodeDepths.end()) {
			assert(maxDepths.at(n.first.NodeID) == nodeDepth2FuncStart.at(n.first.NodeID).size());
			for (auto& depth : nodeDepth2FuncStart.at(n.first.NodeID))
				callchain += "-" + to_string(get<1>(depth.second)) + "(" + to_string(get<0>(depth.second)) + ")";
		}

		string blockName = "Node_" + to_string(n.first.NodeID) + "_" + to_string(n.first.pc);
		string label = to_string(n.first.NodeID) + "#" + to_string(n.first.pc) + "^" + to_string(maxDepths.at(n.first.NodeID));
		const tuple<int, int>& nodeTuple = acIdomNodeDepthChanges.at(n.first);
		string acNodeDepth = "[" + to_string(get<0>(nodeTuple)) + ", " + to_string(get<1>(nodeTuple)) + "]";
		dotFile += blockName + "[label = \"" + label + callchain + acNodeDepth + "\"]\r\n";



		for (auto& chd : n.second) {
			string chdName = "Node_" + to_string(chd.NodeID) + "_" + to_string(chd.pc);
			string content;
			tuple<int, int> t = idomEdgeDepthChanges.at(n.first).at(chd);
			content += "(" + to_string(get<0>(t)) + ", " + to_string(get<1>(t)) + ")";
			const tuple<int, int>& edgeTuple = acIdomEdgeDepthChanges.at(n.first).at(chd);
			content += "[" + to_string(get<0>(edgeTuple)) + ", " + to_string(get<1>(edgeTuple)) + "]";
			string label = "[label = \"" + content + "\"]";
			dotFile += "\t" + blockName + " -> " + chdName + label + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}

void genCFGLocDomDotFile(const map<CFGLoc, set<CFGLoc>>& validDom, const map<int, int>& maxDepths, const map<int, map<int, tuple<int, int>>>& nodeDepths, string fileName, const map<CFGLoc, map<CFGLoc, tuple<int, int>>>& idomEdgeDepthChanges, const map<CFGLoc, int>& loc2DepthChange, const map<CFGLoc, int>& loc2MinDepth, const set<CFGLoc>& rootCFGLocs) {
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : nodeDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : validDom) {
		string callchain;
		if (nodeDepths.find(n.first.NodeID) != nodeDepths.end()) {
			assert(maxDepths.at(n.first.NodeID) == nodeDepth2FuncStart.at(n.first.NodeID).size());
			for (auto& depth : nodeDepth2FuncStart.at(n.first.NodeID))
				callchain += "-" + to_string(get<1>(depth.second)) + "(" + to_string(get<0>(depth.second)) + ")";
		}

		string blockName = "Node_" + to_string(n.first.NodeID) + "_" + to_string(n.first.pc);
		string label = to_string(n.first.NodeID) + "#" + to_string(n.first.pc) + "^" + to_string(maxDepths.at(n.first.NodeID));
		string acNodeDepth = "[" + to_string(loc2DepthChange.at(n.first)) + ", " + to_string(loc2MinDepth.at(n.first)) + "]";
		string color;
		if (rootCFGLocs.find(n.first) != rootCFGLocs.end())
			color += ", color = red";
		dotFile += blockName + "[label = \"" + label + callchain + acNodeDepth + "\"" + color + "]\r\n";



		for (auto& chd : n.second) {
			string chdName = "Node_" + to_string(chd.NodeID) + "_" + to_string(chd.pc);
			string content;
			tuple<int, int> t = idomEdgeDepthChanges.at(n.first).at(chd);
			content += "(" + to_string(get<0>(t)) + ", " + to_string(get<1>(t)) + ")";
			string label = "[label = \"" + content + "\"]";
			dotFile += "\t" + blockName + " -> " + chdName + label + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}

void genCFGLocDomDotFile(const map<CFGLoc, set<CFGLoc>>& validDom, const map<int, int>& maxDepths, const map<int, map<int, tuple<int, int>>>& nodeDepths, string fileName, const map<CFGLoc, map<CFGLoc, tuple<int, int>>>& idomEdgeDepthChanges, const map<CFGLoc, int>& loc2DepthChange, const map<CFGLoc, int>& loc2MinDepth, const set<CFGLoc>& rootCFGLocs, const set<CFGLoc>& removedRoots) {
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : nodeDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : validDom) {
		string callchain;
		if (nodeDepths.find(n.first.NodeID) != nodeDepths.end()) {
			assert(maxDepths.at(n.first.NodeID) == nodeDepth2FuncStart.at(n.first.NodeID).size());
			for (auto& depth : nodeDepth2FuncStart.at(n.first.NodeID))
				callchain += "-" + to_string(get<1>(depth.second)) + "(" + to_string(get<0>(depth.second)) + ")";
		}

		string blockName = "Node_" + to_string(n.first.NodeID) + "_" + to_string(n.first.pc);
		string label = to_string(n.first.NodeID) + "#" + to_string(n.first.pc) + "^" + to_string(maxDepths.at(n.first.NodeID));
		string acNodeDepth = "[" + to_string(loc2DepthChange.at(n.first)) + ", " + to_string(loc2MinDepth.at(n.first)) + "]";
		string color;
		if (removedRoots.find(n.first) != removedRoots.end())
			color += ", color = red";
		else if (rootCFGLocs.find(n.first) != rootCFGLocs.end())
			color += ", color = green";
		dotFile += blockName + "[label = \"" + label + callchain + acNodeDepth + "\"" + color + "]\r\n";



		for (auto& chd : n.second) {
			string chdName = "Node_" + to_string(chd.NodeID) + "_" + to_string(chd.pc);
			string content;
			tuple<int, int> t = idomEdgeDepthChanges.at(n.first).at(chd);
			content += "(" + to_string(get<0>(t)) + ", " + to_string(get<1>(t)) + ")";
			string label = "[label = \"" + content + "\"]";
			dotFile += "\t" + blockName + " -> " + chdName + label + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}


void genDepthDotFile(const map<int, ECFGNode>& nodes, const map<int, int>& maxDepths, string fileName) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : nodes) {
		string blockName = "Node_" + to_string(n.first);
		string label = "Node_" + to_string(n.first) + "#" + to_string(n.second.getStart()) + "-" + to_string(n.second.getEnd());
		string color = "";
		switch (maxDepths.at(n.first)) {
		case 1: {
			color = ", color = red";
			break;
		}
		case 2: {
			color = ", color = blue";
			break;
		}
		case 3: {
			color = ", color = yellow";
			break;
		}
		case 4: {
			color = ", color = purple";
			break;
		}
		case 5: {
			color = ", color = green";
			break;
		}
		case 6: {
			color = ", color = orange";
			break;
		}
		case 7: {
			color = ", color = brown";
			break;
		}
		case 8: {
			color = ", color = cyan";
			break;
		}
		case 9: {
			color = ", color = chocolate";
			break;
		}
		case 10: {
			color = ", color = gold";
			break;
		}
		default:
			break;
		}

		string nodeLabel = "[label = \"" + label + "\"" + color + "]";
		//string nodeLabel = "";
		dotFile += blockName + nodeLabel + "\r\n";
		for (auto p : n.second.getParents()) {
			if (p == -1)
				continue;
			string parentName = "Node_" + to_string(p);

			dotFile += "\t" + parentName + " -> " + blockName + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}

void genAllFunctionBody(const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& blockNodeIDs, const map<int, map<int, tuple<int, int>>>& IDAddrs, map<int, map<int, map<int, tuple<int, int>>>>& funcBodys) {
	for (auto& funcStartAddr : IDAddrs) {
		int startID = -1;
		for(auto& n : funcStartAddr.second)
			if (get<0>(n.second) == funcStartAddr.first) {
				startID = n.first;
				break;
			}

		set<int> IDVisited;

		vector<queue<int>> ques;
		vector<int> funcStartIDs;
		queue<int> first; first.push(startID); ques.push_back(first); funcStartIDs.push_back(startID);
		for (auto& funcStartID : blockNodeIDs.at(funcStartAddr.first)) {
			funcBodys[funcStartAddr.first][funcStartID] = {};
			IDVisited.insert(funcStartID);
			if (funcStartID == startID)
				continue;

			funcStartIDs.push_back(funcStartID);
			queue<int> q;
			q.push(funcStartID);
			ques.push_back(q);
		}

		while (!ques[0].empty()) {
			vector<int> fronts;
			for (size_t i = 0; i < ques.size(); i++) {
				fronts.push_back(ques[i].front());
				ques[i].pop();
				funcBodys[funcStartAddr.first][funcStartIDs[i]][fronts[i]] = funcStartAddr.second.at(fronts[0]);
			}
			//for (auto& f : fronts)
			//	cout << f << " ";
			//cout << endl;
			int jumpID = runtimeNodes.at(fronts[0]).getJumpID();
			int fallsID = runtimeNodes.at(fronts[0]).getFallsID();
			if (jumpID != -1 && IDVisited.find(jumpID) == IDVisited.end() && funcStartAddr.second.find(jumpID) != funcStartAddr.second.end()) {
				for (size_t i = 0; i < ques.size(); i++) {
					int jump = runtimeNodes.at(fronts[i]).getJumpID();
					IDVisited.insert(jump);
					ques[i].push(jump);
				}
			}
			if (fallsID != -1 && IDVisited.find(fallsID) == IDVisited.end() && funcStartAddr.second.find(fallsID) != funcStartAddr.second.end()) {
				for (size_t i = 0; i < ques.size(); i++) {
					int falls = runtimeNodes.at(fronts[i]).getFallsID();
					IDVisited.insert(falls);
					ques[i].push(falls);
				}
			}
		}
	}
}

//nodeDepths : NodeID => (funcStartAddr => <funcStartNodeID, function depth>)
void genFuncRelNodeDepth(const map<int, map<int, map<int, tuple<int, int>>>>& funcBodys, map<int, map<int, tuple<int, int>>>& nodeDepths) {
	for (auto& startAddr : funcBodys)
		for (auto& startNodeID : startAddr.second)
			for (auto& nodeID : startNodeID.second)
				nodeDepths[nodeID.first][startAddr.first] = make_tuple(startNodeID.first, get<1>(nodeID.second));
}

//该函数是查看srcLoc到dstLoc的所有路径上是否存在st_symbolic_value的赋值
bool storageSymAssignExists(const CFGLoc& srcLoc, const CFGLoc& dstLoc, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes) {
	const ECFGNode& srcNode = runtimeNodes.at(srcLoc.NodeID);
	const ECFGNode& dstNode = runtimeNodes.at(dstLoc.NodeID);
	set<int> relInstrAddrs;
	if (srcLoc.NodeID == dstLoc.NodeID) {
		for (auto& i : srcNode.getInstrs())
			if (i.first >= srcLoc.pc && i.first <= dstLoc.pc)
				relInstrAddrs.insert(i.first);
	}
	else {
		for (auto& i : srcNode.getInstrs())
			if (i.first >= srcLoc.pc)
				relInstrAddrs.insert(i.first);
		for (auto& i : dstNode.getInstrs())
			if (i.first <= dstLoc.pc)
				relInstrAddrs.insert(i.first);
		for (auto& id : partEdges)
			if (id.first == srcLoc.NodeID || id.first == dstLoc.NodeID)
				continue;
			else for (auto& i : runtimeNodes.at(id.first).getInstrs())
				relInstrAddrs.insert(i.first);
	}
	for (auto& r : relInstrAddrs)
		if (SSTOREsymInstrs.find(r) != SSTOREsymInstrs.end())
			return true;
	return false;
}

static map<vector<int>, map<int, set<int>>> src2dstPartEdges;
void pruningInvalidSloadDomRelation(const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& reEdges, const map<CFGLoc, CFGLoc>& sloadIdom, const map<int, map<int, tuple<int, int>>>& funcDepths, map<CFGLoc, set<CFGLoc>>& validIdomEdges) {
	bool branchLimit = true;//当该值为true时表明src和dst之间形成的partEdges在原CFG中存在的分支只能是终止节点（即REVERT、INVALID等节点）
	
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : funcDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	for (auto& s : sloadIdom) {
		if (validIdomEdges.find(s.first) == validIdomEdges.end())
			validIdomEdges[s.first] = { };
		bool valid = true;

		int dstNodeID = s.first.NodeID;
		int srcNodeID = s.second.NodeID;
		auto srcDepthIter = nodeDepth2FuncStart.find(srcNodeID);
		auto dstDepthIter = nodeDepth2FuncStart.find(dstNodeID);

		if (srcNodeID != dstNodeID && s.second != CFGLoc(0, 0))
			if (loopExists(srcNodeID, dstNodeID, reEdges))
				valid = false;
			//else if (srcDepthIter != nodeDepth2FuncStart.end() && dstDepthIter == nodeDepth2FuncStart.end()
			//	|| srcDepthIter == nodeDepth2FuncStart.end() && dstDepthIter != nodeDepth2FuncStart.end()
			//	|| srcDepthIter != nodeDepth2FuncStart.end() && dstDepthIter != nodeDepth2FuncStart.end() && srcDepthIter->second.rbegin()->second != dstDepthIter->second.rbegin()->second) {//srcNodeID 和dstNodeID至少应该在一个函数体内部
			//	valid = false;
			//}
			else {
				src2dstPartEdges[{srcNodeID, dstNodeID}] = { };
				map<int, set<int>>& partEdges = src2dstPartEdges.at({ srcNodeID, dstNodeID });
				genPartEdges(reEdges, srcNodeID, dstNodeID, partEdges);
				//srcCFGLoc和dstCFGLoc之间不能存在st_symbolic_value的赋值
				if (storageSymAssignExists(s.second, s.first, partEdges, runtimeNodes))
					valid = false;



				for (auto& n : partEdges) {
					if (n.first == dstNodeID)
						continue;
					int jumpID = runtimeNodes.at(n.first).getJumpID();
					int fallsID = runtimeNodes.at(n.first).getFallsID();
					if (jumpID != -1 && n.second.find(jumpID) == n.second.end()) {
						const ECFGNode& jumpNode = runtimeNodes.at(jumpID);
						if (jumpNode.getParents().size() != 1) {
							valid = false;
							break;
						}

						//以下为一严格限制条件，要求优化子图的分支必须为终止块
						//这一条件是为了防止优化后反而由于走分支路径导致消耗gas增多
						//当然这一条件也会阻止一些优化场景的出现
						
						//当交易执行到REVERT、RETURN、STOP、SELFDESTRUCT终止时，会将多余的gas返还给调用者，所以存在一种情况：刚刚在栈上进行SLOAD相关storage的复制，然后还未执行到下一个SLOAD，程序即终止。之前的复制操作反而会增加gas cost
						//else if (branchLimit && !(jumpNode.getBlockType() == BlockType::REVERT || jumpNode.getBlockType() == BlockType::INVALID || jumpNode.getBlockType() == BlockType::RETURN || jumpNode.getBlockType() == BlockType::STOP || jumpNode.getBlockType() == BlockType::SELFDESTRUCT)) {
						else if (branchLimit && !(jumpNode.getBlockType() == BlockType::INVALID)) {
							valid = false;
							break;
						}
					}
					if (fallsID != -1 && n.second.find(fallsID) == n.second.end()) {
						const ECFGNode& fallsNode = runtimeNodes.at(fallsID);
						if (fallsNode.getParents().size() != 1) {
							valid = false;
							break;
						}

						//以下为一严格限制条件，要求优化子图的分支必须为终止块
						//这一条件是为了防止优化后反而由于走分支路径导致消耗gas增多
						//当然这一条件也会阻止一些优化场景的出现
						//else if (branchLimit && !(fallsNode.getBlockType() == BlockType::REVERT || fallsNode.getBlockType() == BlockType::INVALID || fallsNode.getBlockType() == BlockType::RETURN || fallsNode.getBlockType() == BlockType::STOP || fallsNode.getBlockType() == BlockType::SELFDESTRUCT)) {
						else if (branchLimit && !(fallsNode.getBlockType() == BlockType::INVALID)) {
							valid = false;
							break;
						}
					}

				}

			}
		else if (srcNodeID == dstNodeID) {
			assert(s.second != CFGLoc(0, 0));
			src2dstPartEdges[{srcNodeID, dstNodeID}] = {};
			src2dstPartEdges.at({ srcNodeID, dstNodeID })[srcNodeID] = { };
			//srcCFGLoc和dstCFGLoc之间不能存在st_symbolic_value的赋值
			if (storageSymAssignExists(s.second, s.first, src2dstPartEdges.at({ srcNodeID, dstNodeID }), runtimeNodes))
				valid = false;
		}

		if(valid)
			validIdomEdges[s.second].insert(s.first);
	}
}

static map<PartBasicBlock, int> partblockDepthChange;
static map<PartBasicBlock, int> partblockMinDepth;

static map<PartBasicBlock, int> partblockExceptEndDepthChange;//不包含最后一个指令
static map<PartBasicBlock, int> partblockExceptEndMinDepth;//不包含最后一个指令

static map<PartBasicBlockWithInstrUpdates, int> updatedPartBlockDepthChange;
static map<PartBasicBlockWithInstrUpdates, int> updatedPartBlockMinDepth;

static map<PartBasicBlockWithInstrUpdates, int> updatedPartBlockExceptEndDepthChange;
static map<PartBasicBlockWithInstrUpdates, int> updatedPartBlockExceptEndMinDepth;

//void instrSimCurDepth(string opcode, int& curDepth) {
//	int bytecode = Opcode::getOpcode(opcode);
//	tuple<int, int> op = Opcode::getOperation(bytecode);
//	int delta = get<0>(op);//pop stack
//	int alpha = get<1>(op);//push stack
//	curDepth += delta - alpha;
//}

void instrSimDepth(string opcode, int& curDepth, int& minDepth) {
	int bytecode = Opcode::getOpcode(opcode);
	tuple<int, int> op = Opcode::getOperation(bytecode);
	int delta = get<0>(op);//pop stack
	int alpha = get<1>(op);//push stack

	curDepth -= delta;
	minDepth = minDepth > curDepth ? curDepth : minDepth;
	curDepth += alpha;
}

void bytecodeSimDepth(string bytecodes, int& curDepth, int& minDepth) {
	for (size_t i = 0; i < bytecodes.length();) {
		string bytecode = bytecodes.substr(i, 2);
		size_t byte = stoi(bytecode, nullptr, 16);
		i += 2;
		if(byte >= 0x60 && byte <= 0x7f)
			i += (byte - 0x60 + 1) * 2;
		tuple<int, int> op = Opcode::getOperation(int(byte));
		int delta = get<0>(op);//pop stack
		int alpha = get<1>(op);//push stack

		curDepth -= delta;
		minDepth = minDepth > curDepth ? curDepth : minDepth;
		curDepth += alpha;
	}
}

//<curDepth, minDepth>
tuple<int, int> calPartBasicBlockCurAndMinDepth(const PartBasicBlock& pbb, const map<int, string>& instrs) {
	if (partblockDepthChange.find(pbb) != partblockDepthChange.end() && partblockMinDepth.find(pbb) != partblockMinDepth.end())
		return make_tuple(partblockDepthChange.at(pbb), partblockMinDepth.at(pbb));
	int curDepth = 0;
	int minDepth = 0;
	auto iter = instrs.find(pbb.start);
	for (; iter != instrs.find(pbb.end); iter++) {
		vector<string> temp;
		boost::split(temp, iter->second, boost::is_any_of(" "));
		instrSimDepth(temp[0], curDepth, minDepth);

		//cout << iter->first << " " << iter->second << " curDepth : " << curDepth << ", minDepth : " << minDepth << endl;
	}
	//最后一个指令
	vector<string> temp;
	boost::split(temp, iter->second, boost::is_any_of(" "));
	instrSimDepth(temp[0], curDepth, minDepth);
	//cout << iter->first << " " << iter->second << " curDepth : " << curDepth << ", minDepth : " << minDepth << endl << endl;

	partblockDepthChange.insert(make_pair(pbb, curDepth));
	partblockMinDepth.insert(make_pair(pbb, minDepth));
	return make_tuple(curDepth, minDepth);
}

//<curDepth, minDepth>
tuple<int, int> calPartBasicBlockExceptEndCurAndMinDepth(const PartBasicBlock& pbb, const map<int, string>& instrs) {
	if (partblockExceptEndDepthChange.find(pbb) != partblockExceptEndDepthChange.end() && partblockExceptEndMinDepth.find(pbb) != partblockExceptEndMinDepth.end())
		return make_tuple(partblockExceptEndDepthChange.at(pbb), partblockExceptEndMinDepth.at(pbb));
	int curDepth = 0;
	int minDepth = 0;
	auto iter = instrs.find(pbb.start);
	for (; iter != instrs.find(pbb.end); iter++) {
		vector<string> temp;
		boost::split(temp, iter->second, boost::is_any_of(" "));
		instrSimDepth(temp[0], curDepth, minDepth);

		//cout << iter->first << " " << iter->second << " curDepth : " << curDepth << ", minDepth : " << minDepth << endl;
	}

	partblockExceptEndDepthChange.insert(make_pair(pbb, curDepth));
	partblockExceptEndMinDepth.insert(make_pair(pbb, minDepth));
	return make_tuple(curDepth, minDepth);
}

tuple<int, int> calUpdatedPartBasicBlockCurAndMinDepth(const PartBasicBlockWithInstrUpdates& pbbwiu, const map<int, string>& instrs, bool exceptEnd = false) {
	if (!exceptEnd && updatedPartBlockDepthChange.find(pbbwiu) != updatedPartBlockDepthChange.end() && updatedPartBlockMinDepth.find(pbbwiu) != updatedPartBlockMinDepth.end())
		return make_tuple(updatedPartBlockDepthChange.at(pbbwiu), updatedPartBlockMinDepth.at(pbbwiu));
	if (exceptEnd && updatedPartBlockExceptEndDepthChange.find(pbbwiu) != updatedPartBlockExceptEndDepthChange.end() && updatedPartBlockExceptEndMinDepth.find(pbbwiu) != updatedPartBlockExceptEndMinDepth.end())
		return make_tuple(updatedPartBlockExceptEndDepthChange.at(pbbwiu), updatedPartBlockExceptEndMinDepth.at(pbbwiu));

	int curDepth = 0;
	int minDepth = 0;
	if (pbbwiu.deInstrs.empty() && pbbwiu.updateInstrs.empty()) {
		PartBasicBlock pbb(pbbwiu.blockStart, pbbwiu.start, pbbwiu.end);
		if (!exceptEnd) {
			tuple<int, int> t = calPartBasicBlockCurAndMinDepth(pbb, instrs);
			curDepth = get<0>(t);
			minDepth = get<1>(t);
		}
		if (exceptEnd) {
			tuple<int, int> t = calPartBasicBlockExceptEndCurAndMinDepth(pbb, instrs);
			curDepth = get<0>(t);
			minDepth = get<1>(t);
		}
	}
	else {
		auto iter = instrs.find(pbbwiu.start);
		for (; iter != instrs.find(pbbwiu.end); iter++) {
			if (pbbwiu.deInstrs.find(iter->first) != pbbwiu.deInstrs.end())
				continue;
			else if (pbbwiu.updateInstrs.find(iter->first) != pbbwiu.updateInstrs.end()) {
				bytecodeSimDepth(pbbwiu.updateInstrs.at(iter->first), curDepth, minDepth);
			}
			else {
				vector<string> temp;
				boost::split(temp, iter->second, boost::is_any_of(" "));
				instrSimDepth(temp[0], curDepth, minDepth);
			}

			//cout << iter->first << " " << iter->second << " curDepth : " << curDepth << ", minDepth : " << minDepth << endl;
		}
		
		
		if (!exceptEnd) {//最后一个指令
			if (pbbwiu.deInstrs.find(iter->first) == pbbwiu.deInstrs.end()) {
				if (pbbwiu.updateInstrs.find(iter->first) != pbbwiu.updateInstrs.end()) {
					bytecodeSimDepth(pbbwiu.updateInstrs.at(iter->first), curDepth, minDepth);
				}
				else {
					vector<string> temp;
					boost::split(temp, iter->second, boost::is_any_of(" "));
					instrSimDepth(temp[0], curDepth, minDepth);
				}
			}
			//cout << iter->first << " " << iter->second << " curDepth : " << curDepth << ", minDepth : " << minDepth << endl << endl;
		}
	}
	if (!exceptEnd) {
		updatedPartBlockDepthChange.insert(make_pair(pbbwiu, curDepth));
		updatedPartBlockMinDepth.insert(make_pair(pbbwiu, minDepth));
	}
	else {
		updatedPartBlockExceptEndDepthChange.insert(make_pair(pbbwiu, curDepth));
		updatedPartBlockExceptEndMinDepth.insert(make_pair(pbbwiu, minDepth));
	}
	return make_tuple(curDepth, minDepth);
}

int calUpdatedPathCurDepthChange(const CFGLoc& src, const CFGLoc& dst, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes, const map<int, BlockInstrsChanges*>& nodeID2Changes) {
	if (src.NodeID == dst.NodeID) {
		int blockStart = runtimeNodes.at(src.NodeID).getStart();
		PartBasicBlockWithInstrUpdates pbbwiu(blockStart, src.pc, dst.pc);
		if (nodeID2Changes.find(src.NodeID) != nodeID2Changes.end()) {
			pbbwiu.deInstrs = nodeID2Changes.at(src.NodeID)->deInstrs;
			pbbwiu.updateInstrs = nodeID2Changes.at(src.NodeID)->updateInstrs;
		}
		return get<0>(calUpdatedPartBasicBlockCurAndMinDepth(pbbwiu, runtimeNodes.at(src.NodeID).getInstrs()));
	}
	else {
		vector<int> stack;
		set<int> visited;
		stack.push_back(src.NodeID);
		visited.insert(src.NodeID);
		vector<int> path;
		while (!stack.empty()) {
			int top = stack.back();
			if (top == dst.NodeID) {
				path = stack;
				break;
			}

			bool flag = true;
			for (auto& c : partEdges.at(top))
				if (visited.find(c) == visited.end()) {
					flag = false;
					stack.push_back(c);
					break;
				}
			if (flag)
				stack.pop_back();
		}

		int curDepth = 0;

		const ECFGNode& srcNode = runtimeNodes.at(src.NodeID);
		PartBasicBlockWithInstrUpdates srcPbbwiu(srcNode.getStart(), src.pc, srcNode.getEnd());
		auto iter = nodeID2Changes.find(srcNode.getID());
		if (iter != nodeID2Changes.end()) {
			srcPbbwiu.deInstrs = iter->second->deInstrs;
			srcPbbwiu.updateInstrs = iter->second->updateInstrs;
		}
		curDepth += get<0>(calUpdatedPartBasicBlockCurAndMinDepth(srcPbbwiu, srcNode.getInstrs()));
		for (size_t i = 1; i + 1 < path.size(); i++) {
			const ECFGNode& node = runtimeNodes.at(path[i]);
			PartBasicBlockWithInstrUpdates pbbwiu(node.getStart(), node.getStart(), node.getEnd());
			iter = nodeID2Changes.find(node.getID());
			if (iter != nodeID2Changes.end()) {
				pbbwiu.deInstrs = iter->second->deInstrs;
				pbbwiu.updateInstrs = iter->second->updateInstrs;
			}
			curDepth += get<0>(calUpdatedPartBasicBlockCurAndMinDepth(pbbwiu, node.getInstrs()));
		}
		const ECFGNode& dstNode = runtimeNodes.at(dst.NodeID);
		PartBasicBlockWithInstrUpdates dstPbbwiu(dstNode.getStart(), dstNode.getStart(), dst.pc);
		iter = nodeID2Changes.find(dstNode.getID());
		if (iter != nodeID2Changes.end()) {
			dstPbbwiu.deInstrs = iter->second->deInstrs;
			dstPbbwiu.updateInstrs = iter->second->updateInstrs;
		}
		curDepth += get<0>(calUpdatedPartBasicBlockCurAndMinDepth(dstPbbwiu, dstNode.getInstrs()));
		return curDepth;
	}
}

int calPathCurDepthChange(const CFGLoc& src, const CFGLoc& dst, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes) {
	if (src.NodeID == dst.NodeID) {
		int blockStart = runtimeNodes.at(src.NodeID).getStart();
		PartBasicBlock pbb(blockStart, src.pc, dst.pc);
		return get<0>(calPartBasicBlockCurAndMinDepth(pbb, runtimeNodes.at(src.NodeID).getInstrs()));
	}
	else {
		vector<int> stack;
		set<int> visited;
		stack.push_back(src.NodeID);
		visited.insert(src.NodeID);
		vector<int> path;
		while (!stack.empty()) {
			int top = stack.back();
			if (top == dst.NodeID) {
				path = stack;
				break;
			}

			bool flag = true;
			for (auto& c : partEdges.at(top))
				if (visited.find(c) == visited.end()) {
					flag = false;
					stack.push_back(c);
					break;
				}
			if (flag)
				stack.pop_back();
		}

		int curDepth = 0;

		const ECFGNode& srcNode = runtimeNodes.at(src.NodeID);
		PartBasicBlock srcPbb(srcNode.getStart(), src.pc, srcNode.getEnd());
		curDepth += get<0>(calPartBasicBlockCurAndMinDepth(srcPbb, srcNode.getInstrs()));
		for (size_t i = 1; i + 1 < path.size(); i++) {
			const ECFGNode& node = runtimeNodes.at(path[i]);
			PartBasicBlock pbb(node.getStart(), node.getStart(), node.getEnd());
			curDepth += get<0>(calPartBasicBlockCurAndMinDepth(pbb, node.getInstrs()));
		}
		const ECFGNode& dstNode = runtimeNodes.at(dst.NodeID);
		PartBasicBlock dstPbb(dstNode.getStart(), dstNode.getStart(), dst.pc);
		curDepth += get<0>(calPartBasicBlockCurAndMinDepth(dstPbb, dstNode.getInstrs()));
		return curDepth;
	}
}

void calPartCfgMinDepth(const CFGLoc& dst, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes, int curNodeID, PartBasicBlock curPbb, int& preCurDepth, int& preMinDepth, int& minDepth) {
	tuple<int, int> tuple = calPartBasicBlockCurAndMinDepth(curPbb, runtimeNodes.at(curNodeID).getInstrs());
	int curDepthChange = get<0>(tuple);
	int curMinDepth = get<1>(tuple);

	preMinDepth = preCurDepth + curMinDepth < preMinDepth ? preCurDepth + curMinDepth : preMinDepth;
	preCurDepth += curDepthChange;
	if (partEdges.at(curNodeID).empty()) {
		if (preMinDepth < minDepth)
			minDepth = preMinDepth;
		return;
	}

	int preCurDepthCopy = preCurDepth;
	int preMinDepthCopy = preMinDepth;

	auto chdIter = partEdges.at(curNodeID).begin();
	const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
	PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());
	if (*chdIter == dst.NodeID)
		pbb.end = dst.pc;
	calPartCfgMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepth, preMinDepth, minDepth);

	chdIter++;
	while (chdIter != partEdges.at(curNodeID).end()) {
		const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
		PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());
		if (*chdIter == dst.NodeID)
			pbb.end = dst.pc;
		calPartCfgMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepthCopy, preMinDepthCopy, minDepth);
		chdIter++;
	}
}

void calPartCfgExceptEndMinDepth(const CFGLoc& dst, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes, int curNodeID, PartBasicBlock curPbb, int& preCurDepth, int& preMinDepth, int& minDepth) {
	tuple<int, int> tuple;
	if (curNodeID != dst.NodeID)
		tuple = calPartBasicBlockCurAndMinDepth(curPbb, runtimeNodes.at(curNodeID).getInstrs());
	else//只有在执行最后一个节点时不包含最后一个指令
		tuple = calPartBasicBlockExceptEndCurAndMinDepth(curPbb, runtimeNodes.at(curNodeID).getInstrs());
	int curDepthChange = get<0>(tuple);
	int curMinDepth = get<1>(tuple);

	preMinDepth = preCurDepth + curMinDepth < preMinDepth ? preCurDepth + curMinDepth : preMinDepth;
	preCurDepth += curDepthChange;
	if (partEdges.at(curNodeID).empty()) {
		if (preMinDepth < minDepth)
			minDepth = preMinDepth;
		return;
	}

	int preCurDepthCopy = preCurDepth;
	int preMinDepthCopy = preMinDepth;

	auto chdIter = partEdges.at(curNodeID).begin();
	const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
	PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());

	if (*chdIter == dst.NodeID)
		pbb.end = dst.pc;
	calPartCfgExceptEndMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepth, preMinDepth, minDepth);

	chdIter++;
	while (chdIter != partEdges.at(curNodeID).end()) {
		const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
		PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());

		if (*chdIter == dst.NodeID)
			pbb.end = dst.pc;
		calPartCfgExceptEndMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepthCopy, preMinDepthCopy, minDepth);
		chdIter++;
	}
}

void calUpdatedPartCfgMinDepth(const CFGLoc& dst, const map<int, set<int>>& partEdges, const map<int, ECFGNode>& runtimeNodes, int curNodeID, PartBasicBlock curPbb, int& preCurDepth, int& preMinDepth, int& minDepth, const map<int, BlockInstrsChanges*>& nodeID2Changes, bool exceptEnd = false) {
	tuple<int, int> tuple;
	PartBasicBlockWithInstrUpdates curPbbwiu(curPbb.blockStart, curPbb.start, curPbb.end);
	auto instrChangeIter = nodeID2Changes.find(curNodeID);
	if (instrChangeIter != nodeID2Changes.end()) {
		curPbbwiu.deInstrs = instrChangeIter->second->deInstrs;
		curPbbwiu.updateInstrs = instrChangeIter->second->updateInstrs;
	}
	if (curNodeID != dst.NodeID || !exceptEnd)
		tuple = calUpdatedPartBasicBlockCurAndMinDepth(curPbbwiu, runtimeNodes.at(curNodeID).getInstrs(), false);
	else//只有在执行最后一个节点且exceptEnd为true时不包含最后一个指令
		tuple = calUpdatedPartBasicBlockCurAndMinDepth(curPbbwiu, runtimeNodes.at(curNodeID).getInstrs(), true);
	int curDepthChange = get<0>(tuple);
	int curMinDepth = get<1>(tuple);

	preMinDepth = preCurDepth + curMinDepth < preMinDepth ? preCurDepth + curMinDepth : preMinDepth;
	preCurDepth += curDepthChange;
	if (partEdges.at(curNodeID).empty()) {
		if (preMinDepth < minDepth)
			minDepth = preMinDepth;
		return;
	}

	int preCurDepthCopy = preCurDepth;
	int preMinDepthCopy = preMinDepth;

	auto chdIter = partEdges.at(curNodeID).begin();
	const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
	PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());

	if (*chdIter == dst.NodeID)
		pbb.end = dst.pc;
	calUpdatedPartCfgMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepth, preMinDepth, minDepth, nodeID2Changes, exceptEnd);

	chdIter++;
	while (chdIter != partEdges.at(curNodeID).end()) {
		const ECFGNode& chdNode = runtimeNodes.at(*chdIter);
		PartBasicBlock pbb(chdNode.getStart(), chdNode.getStart(), chdNode.getEnd());

		if (*chdIter == dst.NodeID)
			pbb.end = dst.pc;
		calUpdatedPartCfgMinDepth(dst, partEdges, runtimeNodes, *chdIter, pbb, preCurDepthCopy, preMinDepthCopy, minDepth, nodeID2Changes, exceptEnd);
		chdIter++;
	}
}

int calPartCfgExceptEndMinDepth(const CFGLoc& srcLoc, const CFGLoc& dstLoc, const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& reEdges, vector<int> domChain) {
	int preCurDepth, preMinDepth, minDepth;
	preCurDepth = preMinDepth = minDepth = 0;
	if (domChain.size() == 1) {//src.NodeID == dst.NodeID
		PartBasicBlock curPbb(runtimeNodes.at(srcLoc.NodeID).getStart(), srcLoc.pc, dstLoc.pc);
		calPartCfgExceptEndMinDepth(dstLoc, src2dstPartEdges.at({ srcLoc.NodeID, dstLoc.NodeID }), runtimeNodes, srcLoc.NodeID, curPbb, preCurDepth, preMinDepth, minDepth);
		return minDepth;
	}
	else {
		for (size_t i = 0; i + 1 < domChain.size(); i++) {
			vector<int> src2Dst = { domChain[i], domChain[i + 1] };
			if (src2dstPartEdges.find(src2Dst) == src2dstPartEdges.end()) {
				src2dstPartEdges[src2Dst] = {};
				map<int, set<int>>& partEdges = src2dstPartEdges.at(src2Dst);
				genPartEdges(reEdges, domChain[i], domChain[i + 1], partEdges);
			}
			const ECFGNode& curNode = runtimeNodes.at(domChain[i]);
			const ECFGNode& nextNode = runtimeNodes.at(domChain[i + 1]);
			PartBasicBlock curPbb(curNode.getStart(), curNode.getStart(), curNode.getEnd());
			if (i == 0)
				curPbb.start = srcLoc.pc;
			CFGLoc dst(domChain[i + 1], nextNode.getStart());
			if (i + 1 == domChain.size() - 1)
				dst.pc = dstLoc.pc;
			calPartCfgExceptEndMinDepth(dst, src2dstPartEdges.at(src2Dst), runtimeNodes, domChain[i], curPbb, preCurDepth, preMinDepth, minDepth);
		}

		return minDepth;
	}
}

int calUpdatedPartCfgExceptEndMinDepth(const CFGLoc& srcLoc, const CFGLoc& dstLoc, const map<int, ECFGNode>& runtimeNodes, const map<int, set<int>>& reEdges, vector<int> domChain, const map<int, BlockInstrsChanges*>& nodeID2Changes) {
	int preCurDepth, preMinDepth, minDepth;
	preCurDepth = preMinDepth = minDepth = 0;
	if (domChain.size() == 1) {//src.NodeID == dst.NodeID
		PartBasicBlock curPbb(runtimeNodes.at(srcLoc.NodeID).getStart(), srcLoc.pc, dstLoc.pc);
		calUpdatedPartCfgMinDepth(dstLoc, src2dstPartEdges.at({ srcLoc.NodeID, dstLoc.NodeID }), runtimeNodes, srcLoc.NodeID, curPbb, preCurDepth, preMinDepth, minDepth, nodeID2Changes, true);
		//calPartCfgExceptEndMinDepth(dstLoc, src2dstPartEdges.at({ srcLoc.NodeID, dstLoc.NodeID }), runtimeNodes, srcLoc.NodeID, curPbb, preCurDepth, preMinDepth, minDepth);
		return minDepth;
	}
	else {
		for (size_t i = 0; i + 1 < domChain.size(); i++) {
			vector<int> src2Dst = { domChain[i], domChain[i + 1] };
			if (src2dstPartEdges.find(src2Dst) == src2dstPartEdges.end()) {
				src2dstPartEdges[src2Dst] = {};
				map<int, set<int>>& partEdges = src2dstPartEdges.at(src2Dst);
				genPartEdges(reEdges, domChain[i], domChain[i + 1], partEdges);
			}
			const ECFGNode& curNode = runtimeNodes.at(domChain[i]);
			const ECFGNode& nextNode = runtimeNodes.at(domChain[i + 1]);
			PartBasicBlock curPbb(curNode.getStart(), curNode.getStart(), curNode.getEnd());
			if (i == 0)
				curPbb.start = srcLoc.pc;
			CFGLoc dst(domChain[i + 1], nextNode.getStart());
			if (i + 1 == domChain.size() - 1)
				dst.pc = dstLoc.pc;
			//calPartCfgExceptEndMinDepth(dst, src2dstPartEdges.at(src2Dst), runtimeNodes, domChain[i], curPbb, preCurDepth, preMinDepth, minDepth);
			calUpdatedPartCfgMinDepth(dst, src2dstPartEdges.at(src2Dst), runtimeNodes, domChain[i], curPbb, preCurDepth, preMinDepth, minDepth, nodeID2Changes);
		}

		return minDepth;
	}
}

enum class SloadType { START, MIDDLE, END };
string int2HexString(int i) {
	stringstream ss;
	ss << hex << i;
	string res;
	ss >> res;
	return res;
}
static set<CFGLoc> sloadCFGLocs;
void processSloadInstrs(SloadType sloadType, const CFGLoc& loc, const ECFGNode& node, const map<CFGLoc, int>& loc2DepthChange, const map<CFGLoc, int>& loc2MinDepth, BlockInstrsChanges& bic) {
	sloadCFGLocs.insert(loc);//仅仅是为了统计sload的个数
	const map<int, string>& blockInstrs = node.getInstrs();
	bic.blockStart = node.getStart();
	if (sloadType == SloadType::START) {
		string updateInstrs = int2HexString(Opcode::getOpcode("SLOAD"));

		updateInstrs += int2HexString(Opcode::getOpcode("DUP1"));
		int swapTimes = -loc2MinDepth.at(loc);
		int SWAP1 = Opcode::getOpcode("SWAP1");
		for (int i = swapTimes; i >= 1; i--) {
			int swapOp = SWAP1 - 1 + i;
			updateInstrs += int2HexString(swapOp);
		}
		bic.updateInstrs.insert(make_pair(loc.pc, updateInstrs));
	}
	else {
		auto iter = blockInstrs.find(loc.pc);
		iter--;
		string lastInstrBeforeSload = iter->second;
		int curDepth = loc2DepthChange.at(loc);
		int minDepth = loc2MinDepth.at(loc);
		string updateInstrs;
		if (lastInstrBeforeSload.find("PUSH") != string::npos || lastInstrBeforeSload.find("DUP") != string::npos) {
			bic.deInstrs.insert(iter->first);
		}
		else if (lastInstrBeforeSload.find("SHA3") != string::npos) {
			bic.deInstrs.insert(iter->first);

			int POP = Opcode::getOpcode("POP");
			updateInstrs += int2HexString(POP) + int2HexString(POP);
		}
		else if (lastInstrBeforeSload.find("SWAP") != string::npos) {//SWAPx SLOAD
			//iter--;
			//string secondLastInstr = iter->second;//SLOAD之前的倒数第二条指令
			//if (secondLastInstr != "DUP1")
			//	cout << iter->first << endl;
			//assert(secondLastInstr == "DUP1");
			//bic.deInstrs.insert(iter->first);
			//iter++;
			//bic.deInstrs.insert(iter->first);
			int POP = Opcode::getOpcode("POP");
			updateInstrs += int2HexString(POP);
		}
		else if (lastInstrBeforeSload == "ADD") {// PUSHx/DUPx/SHA3 PUSHx/DUPx ADD
			string secondLastInstr, thirdLastInstr;
			//0xcfe4b035f17209df73198bed33793718b277981b 18184处的ADD指令之前只有一个JUMPDEST指令
			bool eFlag = true;//指示ADD指令所在基本块中在ADD指令之前是否有两个或两个以上的指令
			iter--;
			if (iter == blockInstrs.end())
				eFlag = false;
			else {
				secondLastInstr = iter->second;
				iter--;
				if (iter == blockInstrs.end())
					eFlag = false;
				else
					thirdLastInstr = iter->second;
			}
			//assert(secondLastInstr.find("PUSH") != string::npos || secondLastInstr.find("DUP") != string::npos);
			//assert(thirdLastInstr.find("PUSH") != string::npos || thirdLastInstr.find("DUP") != string::npos || thirdLastInstr == "SHA3");
			if (eFlag && (secondLastInstr.find("PUSH") != string::npos || secondLastInstr.find("DUP") != string::npos) &&
				(thirdLastInstr.find("PUSH") != string::npos || thirdLastInstr.find("DUP") != string::npos || thirdLastInstr == "SHA3")) {
				bic.deInstrs.insert(iter->first);
				iter++;
				bic.deInstrs.insert(iter->first);
				iter++;
				bic.deInstrs.insert(iter->first);
				if (thirdLastInstr == "SHA3") {
					int POP = Opcode::getOpcode("POP");
					updateInstrs += int2HexString(POP) + int2HexString(POP);
				}
			}
			else {
				int POP = Opcode::getOpcode("POP");
				updateInstrs += int2HexString(POP);
				cout << "SLOAD ADD exceptional situation : " << loc.to_string() << endl;
			}
		}
		else {
			int POP = Opcode::getOpcode("POP");
			updateInstrs += int2HexString(POP);
			cout << "SLOAD exceptional situation : " << loc.to_string() << endl;
			//assert(false);
		}

		if (sloadType == SloadType::MIDDLE) {
			int dupDepth = curDepth - minDepth;
			assert(dupDepth >= 1 && dupDepth <= 16);
			int DUP1 = Opcode::getOpcode("DUP1");
			updateInstrs += int2HexString(DUP1 - 1 + dupDepth);
			bic.updateInstrs.insert(make_pair(loc.pc, updateInstrs));
		}
		else {
			//把栈中元素一步步移向栈顶所需操作比较多，没下移一步，均需要三次swap操作
			//以下以stack: 1 2 3 4为例，右边为top
			//1 2 3 4 => 2 1 3 4分三步
			//1 2 3 4 (=>SWAP3) 4 2 3 1 (=>SWAP2) 4 1 3 2 (=>SWAP3) 2 1 3 4
			int moveTimes = curDepth - minDepth - 1;
			int SWAP1 = Opcode::getOpcode("SWAP1");
			assert(moveTimes >= 0);
			if (moveTimes > 0) {
				for (int i = moveTimes; i > 1; i--) {
					int swapH = SWAP1 - 1 + i;
					int swapL = swapH - 1;
					updateInstrs += int2HexString(swapH) + int2HexString(swapL) + int2HexString(swapH);
				}
				updateInstrs += int2HexString(SWAP1);
			}

			bic.updateInstrs.insert(make_pair(loc.pc, updateInstrs));
		}
	}
}

void processSloadGraph(const set<ReSloadChain*>& sloadGraph, const map<CFGLoc, set<CFGLoc>>& validSloadDoms, const map<int, ECFGNode>& runtimeNodes, const map<int, int>& IDom, const map<int, set<int>>& reEdges, map<int, BlockInstrsChanges*>& nodeID2Changes) {
	map<CFGLoc, set<CFGLoc>> newValidSloadDoms;
	map<CFGLoc, set<CFGLoc>> reValidSloadDoms;
	map<CFGLoc, map<CFGLoc, tuple<int, int>>> idomEdgeDepthChanges;//计算两次sload间的控制流所引起的栈空间变化以及所需的最小栈空间
	for (auto& chnPtr : sloadGraph) {
		queue<CFGLoc> que;
		vector<CFGLoc> levelOrder;
		que.push(chnPtr->start);
		while (!que.empty()) {
			CFGLoc front = que.front();
			levelOrder.push_back(front);
			for (auto& chd : validSloadDoms.at(front))
				que.push(chd);
			que.pop();
		}

		for (auto& pnt : levelOrder) {
			if (reValidSloadDoms.find(pnt) == reValidSloadDoms.end())
				reValidSloadDoms[pnt] = { };
			newValidSloadDoms.insert(make_pair(pnt, validSloadDoms.at(pnt)));
			for (auto& chd : validSloadDoms.at(pnt)) {
				reValidSloadDoms[chd].insert(pnt);
				if (pnt == CFGLoc(0, 0)) {
					idomEdgeDepthChanges[pnt][chd] = make_tuple(0, 0);
				}
				else {
					int depthChange = 0;
					int minDepth = 0;

					const map<int, set<int>>& partEdges = src2dstPartEdges.at({ pnt.NodeID, chd.NodeID });
					depthChange = calUpdatedPathCurDepthChange(pnt, chd, partEdges, runtimeNodes, nodeID2Changes);

					int minDepthExceptEnd = 0;
					vector<int> domChain;
					int up = chd.NodeID;
					domChain.push_back(up);
					while (up != pnt.NodeID) {
						up = IDom.at(up);
						domChain.push_back(up);
					}
					reverse(domChain.begin(), domChain.end());

					minDepthExceptEnd = calUpdatedPartCfgExceptEndMinDepth(pnt, chd, runtimeNodes, reEdges, domChain, nodeID2Changes);
					//assert(minDepth == minDepthExceptEnd);
					//cout << "minDepth " << minDepth << ", minDepthExceptEnd " << minDepthExceptEnd << endl;
					//idomEdgeDepthChanges[pnt.first][chd] = make_tuple(depthChange, minDepth);
					idomEdgeDepthChanges[pnt][chd] = make_tuple(depthChange, minDepthExceptEnd);
				}
			}
		}
	}

	//以下的计算是假定从某一根CFGLoc开始的冗余sload链（还可能是树）所需的最小栈空间是一致的（这样是为了避免在消除冗余sload的时候还需要调整冗余slod复制的位置）
	set<CFGLoc> rootCFGLocs;//不包括CFGLoc(0, 0)，所有冗余sload开始的位置
	map<CFGLoc, int> rootCFGLocMinDepth;
	map<CFGLoc, int> rootCFGLocMaxDepthChange;

	map<CFGLoc, CFGLoc> loc2Root;
	map<CFGLoc, int> loc2DepthChange;
	for (auto& n : reValidSloadDoms)
		if (n.first == CFGLoc(0, 0))
			continue;
		else if (n.second.empty() || (n.second.size() == 1 && *n.second.begin() == CFGLoc(0, 0)))
			rootCFGLocs.insert(n.first);
	for (auto& rt : rootCFGLocs) {
		queue<CFGLoc> que;
		que.push(rt);
		rootCFGLocMaxDepthChange[rt] = 0;
		rootCFGLocMinDepth[rt] = 0;

		loc2DepthChange[rt] = 0;
		loc2Root[rt] = rt;
		while (!que.empty()) {
			CFGLoc front = que.front();
			que.pop();
			set<CFGLoc> removedChd;
			for (auto& chd : newValidSloadDoms.at(front)) {
				int preCurDepth = loc2DepthChange.at(front);
				int curRootMinDepth = rootCFGLocMinDepth.at(loc2Root.at(front));

				const tuple<int, int>& edgeTuple = idomEdgeDepthChanges.at(front).at(chd);
				int curEdgeDepthChange = get<0>(edgeTuple);
				int curEdgeMinDepth = get<1>(edgeTuple);

				int tempMinDepth = preCurDepth + curEdgeMinDepth < curRootMinDepth ? preCurDepth + curEdgeMinDepth : curRootMinDepth;
				int tempMaxCurDepth = preCurDepth + curEdgeDepthChange > rootCFGLocMaxDepthChange.at(loc2Root.at(front)) ? preCurDepth + curEdgeDepthChange : rootCFGLocMaxDepthChange.at(loc2Root.at(front));

				if (tempMinDepth < -16 || tempMaxCurDepth - tempMinDepth > 16) {//该节点应成为root节点
					rootCFGLocMaxDepthChange[chd] = 0;
					rootCFGLocMinDepth[chd] = 0;

					loc2DepthChange[chd] = 0;
					loc2Root[chd] = chd;

					removedChd.insert(chd);
				}
				else {
					loc2Root[chd] = loc2Root.at(front);
					loc2DepthChange[chd] = preCurDepth + curEdgeDepthChange;

					rootCFGLocMaxDepthChange.at(loc2Root.at(chd)) = tempMaxCurDepth;
					rootCFGLocMinDepth.at(loc2Root.at(chd)) = tempMinDepth;
				}
				que.push(chd);
			}

			//保证产生的新root在validSloadDoms中没有入边
			for (auto& c : removedChd)
				newValidSloadDoms.at(front).erase(c);

		}

	}

	//添加由于深度限制产生的新root
	for (auto& r : rootCFGLocMaxDepthChange)
		if (rootCFGLocs.find(r.first) == rootCFGLocs.end())
			rootCFGLocs.insert(r.first);

	//同一冗余sload链上的所有CFGLoc共享同一minDepth
	map<CFGLoc, int> loc2MinDepth;
	//set<int> allLocs;
	for (auto& loc : newValidSloadDoms)
		if (loc.first == CFGLoc(0, 0)) {
			loc2DepthChange[loc.first] = 0;
			loc2MinDepth[loc.first] = 0;
		}
		else
			loc2MinDepth[loc.first] = rootCFGLocMinDepth.at(loc2Root.at(loc.first));
	//genCFGLocDomDotFile(validSloadDoms, maxDepths, funcDepths, name + ".validSloadDomWithDepth.dot", idomEdgeDepthChanges, loc2DepthChange, loc2MinDepth, rootCFGLocs);

	map<CFGLoc, set<CFGLoc>> rootEndLocs;//key值为有效的冗余sload链的起始CFGLoc
	//rootCFGLocs和rootEndLocs的key值集合不一定相同
	//rootCFGLocs包含所有可能是root的CFGLoc(单个CFGLoc也算)

	for (auto& loc : newValidSloadDoms)
		if (loc.second.empty() && rootCFGLocs.find(loc.first) == rootCFGLocs.end()) {
			rootEndLocs[loc2Root.at(loc.first)].insert(loc.first);
		}

	cout << "add " << rootEndLocs.size() << " Redundant Sload chain" << endl;
	for (auto& rtLoc : rootEndLocs) {
		queue<CFGLoc> que;
		que.push(rtLoc.first);
		bool isStart = true;
		while (!que.empty()) {
			bool isEnd = false;
			CFGLoc front = que.front();
			que.pop();

			SloadType frontType;
			if (isStart) {
				frontType = SloadType::START;
				isStart = false;
			}
			else if (newValidSloadDoms.at(front).empty())
				frontType = SloadType::END;
			else
				frontType = SloadType::MIDDLE;

			if (nodeID2Changes.find(front.NodeID) == nodeID2Changes.end())
				nodeID2Changes[front.NodeID] = new BlockInstrsChanges;
			processSloadInstrs(frontType, front, runtimeNodes.at(front.NodeID), loc2DepthChange, loc2MinDepth, *nodeID2Changes.at(front.NodeID));

			for (auto& chd : newValidSloadDoms.at(front))
				que.push(chd);
		}
	}
}

void mergePartEdges(map<int, set<int>>& res, const map<int, set<int>>& edges) {
	for (auto& i : edges)
		if (res.find(i.first) == res.end())
			res.insert(make_pair(i.first, i.second));
		else for (auto& c : i.second)
			res.at(i.first).insert(c);
}
bool intersect(const PartBasicBlock& pbb1, const PartBasicBlock& pbb2) {
	if (pbb1.start >= pbb2.start && pbb1.start <= pbb2.end ||
		pbb1.end >= pbb2.start && pbb1.end <= pbb2.end)
		return true;
	else
		return false;
}
bool intersect(const ReSloadChain& r1, const ReSloadChain& r2, const map<int, ECFGNode>& runtimeNodes) {
	for(auto& n : r1.partEdges)
		if (r1.pbbs.find(n.first) != r1.pbbs.end()) {
			if (r2.partEdges.find(n.first) != r2.partEdges.end())
				if (r2.pbbs.find(n.first) == r2.pbbs.end())
					return true;
				else if (intersect(r1.pbbs.at(n.first), r2.pbbs.at(n.first)))
					return true;
		}
		else if (r2.partEdges.find(n.first) != r2.partEdges.end())
			return true;
	return false;
}

void Contract::redundantSLOADOptimize(set<int> allReInvAddrs, set<int> invIDs, map<int, int> invRelatedInstrStart, map<int, int> invTypes, string newBinFileName) {
	map<int, set<int>> edges;
	map<int, set<int>> reEdges;
	for (auto& i : runtimeNodes) {
		edges[i.first] = { };
		reEdges[i.first] = { };
		if (i.second.getJumpID() != -1)
			edges.at(i.first).insert(i.second.getJumpID());
		if (i.second.getFallsID() != -1)
			edges.at(i.first).insert(i.second.getFallsID());
		for (auto& pnt : i.second.getParents())
			if (pnt != -1)
				reEdges.at(i.first).insert(pnt);
	}

	map<int, int> IDom = genIDom(edges);

	map<string, set<CFGLoc>> sload;//st_index => 读取st_index的SLOAD指令的位置信息
	map<string, set<CFGLoc>> sstore;//st_index => 写入st_index的SSTORE指令的位置信息
	map<string, map<int, set<CFGLoc>>> sameSload;//st_index => (读取st_index的SLOAD指令在生成SSA时的编号，编号相同代表读取的是相同的值) => 读取相同的st_index的所有SLOAD指令的位置信息
	for(auto& st : storageInstrs)
		for (auto& info : st.second) {
			string instr = runtimeNodes.at(info.NodeID).getInstrs().at(info.pc);
			if (instr == "SLOAD") {
				sload[st.first].insert(CFGLoc(info));
				int loadIdx = runtimeNodes.at(info.NodeID).getLoadIndex(info.pc);
				sameSload[st.first][loadIdx].insert(CFGLoc(info));
			}
			else if (instr == "SSTORE")
				sstore[st.first].insert(CFGLoc(info));
			else
				assert(false);
		}

	map<CFGLoc, set<CFGLoc>> sloadDoms;
	for(auto& stIdx : sameSload)
		for (auto& idxNo : stIdx.second) {
			for (auto& cur : idxNo.second)
				for (auto& next : idxNo.second)
					if (cur == next)
						continue;
					else if (dominates(cur, next, IDom)) {
						sloadDoms[cur].insert(next);
						if (sloadDoms.find(next) == sloadDoms.end())
							sloadDoms[next] = { };
					}

			//for (auto& dom : sloadDoms) {
			//	cout << "Node_" << dom.first.NodeID << " pc " << dom.first.pc << endl;
			//	for (auto& chd : dom.second)
			//		cout << "\tNode_" << chd.NodeID << " pc " << chd.pc << endl;
			//}
		}

	set<int> potentialTgt;
	genFuncInTgt(runtimeNodes, blocks, potentialTgt);

	map<int, map<int, tuple<int, int>>> IDAddrs;
	map<int, map<int, int>> funcEnds;
	map<int, map<int, vector<int>>> funcTopLevelIDs;
	for (auto& in : potentialTgt) {
		if (IDAddrs.find(in) != IDAddrs.end())
			continue;
		int firstID = *blockNodeIDs.at(in).begin();
		map<int, vector<int>> left;
		map<int, vector<int>> funcIDs;
		genFuncbodyBlocks(runtimeNodes, in, firstID, IDAddrs, funcEnds, funcTopLevelIDs, potentialTgt, 0, left, funcIDs);
	}
	map<int, map<int, map<int, tuple<int, int>>>> funcBodys;
	genAllFunctionBody(runtimeNodes, blockNodeIDs, IDAddrs, funcBodys);

	map<int, int> maxDepths;//NodeID => 该NodeID所在的最大函数深度
	for (auto& bodys : funcBodys) {
		for (auto& body : bodys.second)
			for (auto& node : body.second)
				if (maxDepths.find(node.first) == maxDepths.end())
					maxDepths[node.first] = get<1>(node.second) + 1;
				else {
					int depth = get<1>(node.second) + 1;
					if (depth > maxDepths.at(node.first))
						maxDepths.at(node.first) = depth;
				}
	}
	for (auto& n : runtimeNodes)
		if (maxDepths.find(n.first) == maxDepths.end())
			maxDepths[n.first] = 0;

	map<CFGLoc, CFGLoc> cfgLocIdom;
	genCFGLocIDom(sloadDoms, cfgLocIdom);//cfgLocIdom的key值集合无CFGLoc(0, 0)，value集合有CFGLoc(0, 0)

	string name = this->name;
	name[name.find_last_of(':')] = '.';
	
	genDepthDotFile(runtimeNodes, maxDepths, name + ".depth.dot");

	//funcDepths : NodeID => (funcStartAddr => <funcStartNodeID, function depth>)
	map<int, map<int, tuple<int, int>>> funcDepths;
	genFuncRelNodeDepth(funcBodys, funcDepths);
	//nodeDepth2FuncStart : NodeID => (function depth => <funcStartAddr, funcStartNodeID>)
	map<int, map<int, tuple<int, int>>> nodeDepth2FuncStart;
	for (auto& n : funcDepths)
		for (auto& funcStart : n.second)
			nodeDepth2FuncStart[n.first][get<1>(funcStart.second)] = make_tuple(funcStart.first, get<0>(funcStart.second));

	//由于进行assertion检查时会删除assertion相关指令序列，序列中可能包含有SLOAD，因此我们需要把由于冗余assertion已经被删除的SLOAD指令可能存在的重复读关系删掉
	set<CFGLoc> deletedSloadLocs;
	for (auto& invID : invIDs) {
		int invAddr = runtimeNodes.at(invID).getStart();
		int instrStart = invRelatedInstrStart.at(invAddr);
		//由invID一路向上找直接包含instrStart的支配节点
		int domID = IDom.at(invID);
		while (domID != -1) {
			int nodeStart = runtimeNodes.at(domID).getStart();
			int nodeEnd = runtimeNodes.at(domID).getEnd();
			if (nodeStart <= instrStart && instrStart <= nodeEnd)
				break;
			domID = IDom.at(domID);
		}
		map<int, set<int>> partEdges;
		genPartEdges(reEdges, domID, invID, partEdges);
		for (auto& id : partEdges) {
			int start;
			int end = runtimeNodes.at(id.first).getEnd();
			if (id.first == domID)
				start = instrStart;
			else
				start = runtimeNodes.at(id.first).getStart();
			auto iter = instructions.find(start);
			while (iter->first <= end) {
				if (iter->second == "SLOAD")
					deletedSloadLocs.insert(CFGLoc(id.first, iter->first));
				iter++;
			}
		}
	}


	set<CFGLoc> removedIdomRel;
	for (auto& domRel : cfgLocIdom) {
		if (deletedSloadLocs.find(domRel.first) != deletedSloadLocs.end() || deletedSloadLocs.find(domRel.second) != deletedSloadLocs.end())
			removedIdomRel.insert(domRel.first);
	}
	for (auto& r : removedIdomRel) {
		displayYellowMsg("Removed CFGLoc\t" + r.to_string() + " " + cfgLocIdom.at(r).to_string());
		cfgLocIdom.erase(r);
	}
	removedIdomRel.clear();

	//常理来说，一个函数调用深度为0的节点所在的基本块在生成CFG的过程中只能生成一个节点，但部分测试用例有悖于此
	//0x3528C164e3fCA20E2333Cf58Ab4B1c99DeF83347 的3263对应的INVALID节点地址为13986，而13986节点有48个Node
	//为了避免上述情况可能会影响冗余sload的优化，将此类节点的出入边均剪除
	//0xc7e0cd1a9f4514d4d4e5044695cc1716b430153e和0xee132ac9eb7dc7518cb06a17bf1e31a541fb2cbc
	//以上两例出现bug的原因在于最开始即将跳入函数体的JUMP [in] block在CFG中生成的Node数大于1
	

	//用于修正0x791d406b20a7d93c0945b0d9d7abf323772397c9出现的bug : 出现连续两个深度相同的函数体
	//Node_79(2065-2094)和Node_80(5434-5512)均为函数体起始节点，但是callChain只能显示到调用Node_79
	set<int> pendingNodes;
	for (auto& locIdom : cfgLocIdom) {
		set<int> nodeIDs;
		nodeIDs.insert(locIdom.first.NodeID);
		nodeIDs.insert(locIdom.second.NodeID);
		for (auto& id : nodeIDs) {
			int blockStart = runtimeNodes.at(id).getStart();
			int maxDepth = maxDepths.at(id);
			if (maxDepth == 0) {
				if (blockNodeIDs.at(blockStart).size() > 1)
					removedIdomRel.insert(locIdom.first);
			}
			else {
				auto dths = nodeDepth2FuncStart.at(id);
				const tuple<int, int>& tle = dths.rbegin()->second;//取函数调用链最开始进入的函数体
				int firstFuncStartNode = get<1>(tle);
				for (auto& pnt : runtimeNodes.at(firstFuncStartNode).getParents()) {
					assert(maxDepths.at(pnt) == 0);
					//cout << "curNodeID " << id << ", first JumpIn Node " << pnt << endl;
					if (blockNodeIDs.at(runtimeNodes.at(pnt).getStart()).size() > 1)
						removedIdomRel.insert(locIdom.first);
				}
				pendingNodes.insert(id);
			}
		}
		//int firstNodeID = locIdom.first.NodeID;
		//int firstBlock = runtimeNodes.at(firstNodeID).getStart();
		//int firstMaxDepth = maxDepths.at(firstNodeID);
		//if (firstMaxDepth == 0 && blockNodeIDs.at(firstBlock).size() > 1) {
		//	removedIdomRel.insert(locIdom.first);
		//	continue;
		//}

		//int secondNodeID = locIdom.second.NodeID;
		//int secondBlock = runtimeNodes.at(secondNodeID).getStart();
		//int secondMaxDepth = maxDepths.at(secondNodeID);
		//if (secondMaxDepth == 0 && blockNodeIDs.at(secondBlock).size() > 1)
		//	removedIdomRel.insert(locIdom.first);
	}
	for (auto& r : removedIdomRel) {
		displayPurpleMsg("Removed CFGLoc\t" + r.to_string() + " " + cfgLocIdom.at(r).to_string());
		cfgLocIdom.erase(r);
	}
	removedIdomRel.clear();

	map<int, vector<int>> paths;
	getDstIDPaths(edges, pendingNodes, paths);
	set<CFGLoc> standaloneCFGLocs;
	for (auto& locIdom : cfgLocIdom) {
		if (standaloneCFGLocs.find(locIdom.first) != standaloneCFGLocs.end() || standaloneCFGLocs.find(locIdom.second) != standaloneCFGLocs.end())
			removedIdomRel.insert(locIdom.first);
		else {
			map<int, set<CFGLoc>> locs;
			if (maxDepths.at(locIdom.first.NodeID) > 0)
				locs[locIdom.first.NodeID].insert(locIdom.first);
			if (maxDepths.at(locIdom.second.NodeID) > 0)
				locs[locIdom.second.NodeID].insert(locIdom.second);
			for (auto& loc : locs) {
				vector<int> callIDChain;
				vector<int> callAddrChain;
				genCallChain(loc.first, paths.at(loc.first), runtimeNodes, IDAddrs, funcEnds, callAddrChain, callIDChain);
				callIDChain.pop_back();
				callAddrChain.pop_back();
				assert(int(callIDChain.size()) == maxDepths.at(loc.first));

				vector<int> jumpInTgtIDs;
				for (auto& i : callIDChain)
					jumpInTgtIDs.push_back(runtimeNodes.at(i).getJumpID());

				vector<int> funcStartIDs;
				for (auto& dths : nodeDepth2FuncStart.at(loc.first))
					funcStartIDs.push_back(get<1>(dths.second));
				reverse(funcStartIDs.begin(), funcStartIDs.end());

				if (jumpInTgtIDs != funcStartIDs) {
					for (auto& l : loc.second)
						standaloneCFGLocs.insert(l);
					removedIdomRel.insert(locIdom.first);
				}
			}
		}
	}
	for (auto& r : removedIdomRel) {
		displayBlueMsg("Removed CFGLoc\t" + r.to_string() + " " + cfgLocIdom.at(r).to_string());
		cfgLocIdom.erase(r);
	}

	genCFGLocDomDotFile(cfgLocIdom, maxDepths, funcDepths, name + ".CFGLoc.dot");

	map<CFGLoc, set<CFGLoc>> validSloadDoms;
	pruningInvalidSloadDomRelation(runtimeNodes, reEdges, cfgLocIdom, funcDepths, validSloadDoms);//删除冗余sload链中的无效边
	genCFGLocDomDotFile(validSloadDoms, maxDepths, funcDepths, name + ".validSloadDom.dot");
	
	map<CFGLoc, map<CFGLoc, tuple<int, int>>> idomEdgeDepthChanges;//计算两次sload间的控制流所引起的栈空间变化以及所需的最小栈空间
	for (auto& pnt : validSloadDoms) {
		for (auto& chd : pnt.second) {
			if (pnt.first == CFGLoc(0, 0)) {
				idomEdgeDepthChanges[pnt.first][chd] = make_tuple(0, 0);
			}
			else {
				int depthChange = 0;
				int minDepth = 0;

				const map<int, set<int>>& partEdges = src2dstPartEdges.at({ pnt.first.NodeID, chd.NodeID });
				depthChange = calPathCurDepthChange(pnt.first, chd, partEdges, runtimeNodes);

				//int preCurDepth = 0;
				//int preMinDepth = 0;
				//const ECFGNode& pntNode = runtimeNodes.at(pnt.first.NodeID);
				//const ECFGNode& chdNode = runtimeNodes.at(chd.NodeID);
				//PartBasicBlock pbb(pntNode.getStart(), pnt.first.pc, pntNode.getEnd());
				//if (pnt.first.NodeID == chd.NodeID)
				//	pbb.end = chd.pc;
				//calPartCfgMinDepth(chd, partEdges, runtimeNodes, pnt.first.NodeID, pbb, preCurDepth, preMinDepth, minDepth);

				int minDepthExceptEnd = 0;
				vector<int> domChain;
				int up = chd.NodeID;
				domChain.push_back(up);
				while (up != pnt.first.NodeID) {
					up = IDom.at(up);
					domChain.push_back(up);
				}
				reverse(domChain.begin(), domChain.end());

				minDepthExceptEnd = calPartCfgExceptEndMinDepth(pnt.first, chd, runtimeNodes, reEdges, domChain);
				//assert(minDepth == minDepthExceptEnd);
				//cout << "minDepth " << minDepth << ", minDepthExceptEnd " << minDepthExceptEnd << endl;
				//idomEdgeDepthChanges[pnt.first][chd] = make_tuple(depthChange, minDepth);
				idomEdgeDepthChanges[pnt.first][chd] = make_tuple(depthChange, minDepthExceptEnd);
			}
		}
	}

	map<CFGLoc, set<CFGLoc>> reValidSloadDoms;
	for (auto& pnt : validSloadDoms) {
		if (reValidSloadDoms.find(pnt.first) == reValidSloadDoms.end())
			reValidSloadDoms[pnt.first] = { };
		for (auto& chd : pnt.second)
			reValidSloadDoms[chd].insert(pnt.first);
	}

	//以下的计算是假定从某一根CFGLoc开始的冗余sload链（还可能是树）所需的最小栈空间是一致的（这样是为了避免在消除冗余sload的时候还需要调整冗余slod复制的位置）
	set<CFGLoc> rootCFGLocs;//不包括CFGLoc(0, 0)，所有冗余sload开始的位置
	map<CFGLoc, int> rootCFGLocMinDepth;
	map<CFGLoc, int> rootCFGLocMaxDepthChange;

	map<CFGLoc, CFGLoc> loc2Root;
	map<CFGLoc, int> loc2DepthChange;
	for (auto& n : reValidSloadDoms)
		if (n.first == CFGLoc(0, 0))
			continue;
		else if (n.second.empty() || (n.second.size() == 1 && *n.second.begin() == CFGLoc(0, 0)))
			rootCFGLocs.insert(n.first);
	for (auto& rt : rootCFGLocs) {
		queue<CFGLoc> que;
		que.push(rt);
		rootCFGLocMaxDepthChange[rt] = 0;
		rootCFGLocMinDepth[rt] = 0;

		loc2DepthChange[rt] = 0;
		loc2Root[rt] = rt;
		while (!que.empty()) {
			CFGLoc front = que.front();
			que.pop();
			set<CFGLoc> removedChd;
			for (auto& chd : validSloadDoms.at(front)) {
				int preCurDepth = loc2DepthChange.at(front);
				int curRootMinDepth = rootCFGLocMinDepth.at(loc2Root.at(front));

				const tuple<int, int>& edgeTuple = idomEdgeDepthChanges.at(front).at(chd);
				int curEdgeDepthChange = get<0>(edgeTuple);
				int curEdgeMinDepth = get<1>(edgeTuple);

				int tempMinDepth = preCurDepth + curEdgeMinDepth < curRootMinDepth ? preCurDepth + curEdgeMinDepth : curRootMinDepth;
				int tempMaxCurDepth = preCurDepth + curEdgeDepthChange > rootCFGLocMaxDepthChange.at(loc2Root.at(front)) ? preCurDepth + curEdgeDepthChange : rootCFGLocMaxDepthChange.at(loc2Root.at(front));

				if (tempMinDepth < -16 || tempMaxCurDepth - tempMinDepth > 16) {//该节点应成为root节点
					rootCFGLocMaxDepthChange[chd] = 0;
					rootCFGLocMinDepth[chd] = 0;
					
					loc2DepthChange[chd] = 0;
					loc2Root[chd] = chd;

					removedChd.insert(chd);
				}
				else {
					loc2Root[chd] = loc2Root.at(front);
					loc2DepthChange[chd] = preCurDepth + curEdgeDepthChange;

					rootCFGLocMaxDepthChange.at(loc2Root.at(chd)) = tempMaxCurDepth;
					rootCFGLocMinDepth.at(loc2Root.at(chd)) = tempMinDepth;
				}
				que.push(chd);
			}

			//保证产生的新root在validSloadDoms中没有入边
			for (auto& c : removedChd)
				validSloadDoms.at(front).erase(c);

		}

	}
	
	//添加由于深度限制产生的新root
	for (auto& r : rootCFGLocMaxDepthChange)
		if (rootCFGLocs.find(r.first) == rootCFGLocs.end())
			rootCFGLocs.insert(r.first);

	//同一冗余sload链上的所有CFGLoc共享同一minDepth
	map<CFGLoc, int> loc2MinDepth;
	//set<int> allLocs;
	for (auto& loc : validSloadDoms)
		if (loc.first == CFGLoc(0, 0)) {
			loc2DepthChange[loc.first] = 0;
			loc2MinDepth[loc.first] = 0;
		}
		else
			loc2MinDepth[loc.first] = rootCFGLocMinDepth.at(loc2Root.at(loc.first));
	genCFGLocDomDotFile(validSloadDoms, maxDepths, funcDepths, name + ".validSloadDomWithDepth.dot", idomEdgeDepthChanges, loc2DepthChange, loc2MinDepth, rootCFGLocs);

	map<CFGLoc, set<CFGLoc>> rootEndLocs;//key值为有效的冗余sload链的终止CFGLoc
	for(auto& loc : validSloadDoms)
		if (loc.second.empty() && rootCFGLocs.find(loc.first) == rootCFGLocs.end()) {
			rootEndLocs[loc2Root.at(loc.first)].insert(loc.first);
		}
	
	map<CFGLoc, ReSloadChain*> rootSloadChain;
	for (auto& r : rootEndLocs) {
		CFGLoc firstEndLoc = *r.second.begin();
		if (firstEndLoc.NodeID == r.first.NodeID) {
			assert(r.second.size() == 1);
			ReSloadChain* rsc = new ReSloadChain;
			rsc->start = r.first;
			rsc->end = r.second;
			rsc->partEdges[r.first.NodeID] = { };
			rsc->pbbs.insert(make_pair(r.first.NodeID, PartBasicBlock(runtimeNodes.at(r.first.NodeID).getStart(), r.first.pc, firstEndLoc.pc)));

			rootSloadChain.insert(make_pair(r.first, rsc));
		}
		else {
			ReSloadChain* rsc = new ReSloadChain;
			rsc->start = r.first;
			rsc->end = r.second;
			map<int, int> edges;
			queue<CFGLoc> que;
			que.push(rsc->start);
			while (!que.empty()) {
				CFGLoc front = que.front();
				que.pop();
				for (auto& chd : validSloadDoms.at(front)) {
					que.push(chd);
					edges[front.NodeID] = chd.NodeID;
				}
			}
			rsc->partEdges = {};
			for(auto& e : edges)
				mergePartEdges(rsc->partEdges, src2dstPartEdges.at({e.first, e.second}));

			rsc->pbbs.insert(make_pair(r.first.NodeID, PartBasicBlock(runtimeNodes.at(r.first.NodeID).getStart(), r.first.pc, runtimeNodes.at(r.first.NodeID).getEnd())));
			for (auto& e : r.second) {
				const ECFGNode& endNode = runtimeNodes.at(e.NodeID);
				rsc->pbbs.insert(make_pair(e.NodeID, PartBasicBlock(endNode.getStart(), endNode.getStart(), e.pc)));
			}

			rootSloadChain.insert(make_pair(r.first, rsc));
		}
	}

	
	//目前冗余sload链存在重合的情况先简单处理：弃之不用
	set<ReSloadChain*> usableChains;
	set<CFGLoc> removedRoot;
	map<ReSloadChain*, set<ReSloadChain*>> disjointChainGraph;
	for (auto& c : rootSloadChain) {
		bool inter = false;
		for (auto& chnPtr : usableChains)
			if (intersect(*c.second, *chnPtr, runtimeNodes)) {
				inter = true;
				break;
			}
		if (!inter)
			usableChains.insert(c.second);
		else {
			removedRoot.insert(c.first);
			ReSloadChain* keyChainPtr = nullptr;
			bool isIntersect = false;
			for (auto& graphPtr : disjointChainGraph) {
				for (auto& chnPtr : graphPtr.second) {
					if (intersect(*c.second, *chnPtr, runtimeNodes)) {
						isIntersect = true;
						break;
					}
				}
				if (!isIntersect) {
					keyChainPtr = graphPtr.first;
					break;
				}
			}

			if (keyChainPtr == nullptr)
				disjointChainGraph[c.second].insert(c.second);
			else
				disjointChainGraph[keyChainPtr].insert(c.second);
		}
	}
	cout << "First Usable Redundant Sload chain Number : " << usableChains.size() << endl;
	genCFGLocDomDotFile(validSloadDoms, maxDepths, funcDepths, name + ".validSloadChain.dot", idomEdgeDepthChanges, loc2DepthChange, loc2MinDepth, rootCFGLocs, removedRoot);

	//这里已经综合了一个Node内部所有可能的变化（一个Node内部可能存在多个冗余SLOAD）
	map<int, BlockInstrsChanges*> nodeID2Changes;
	for (auto& r : rootSloadChain)
		if (removedRoot.find(r.first) != removedRoot.end())
			continue;
		else {
			queue<CFGLoc> que;
			que.push(r.first);
			bool isStart = true;
			while (!que.empty()) {
				bool isEnd = false;
				CFGLoc front = que.front();
				que.pop();

				SloadType frontType;
				if (isStart) {
					frontType = SloadType::START;
					isStart = false;
				}
				else if (validSloadDoms.at(front).empty())
					frontType = SloadType::END;
				else
					frontType = SloadType::MIDDLE;

				if (nodeID2Changes.find(front.NodeID) == nodeID2Changes.end())
					nodeID2Changes[front.NodeID] = new BlockInstrsChanges;
				processSloadInstrs(frontType, front, runtimeNodes.at(front.NodeID), loc2DepthChange, loc2MinDepth, *nodeID2Changes.at(front.NodeID));

				for (auto& chd : validSloadDoms.at(front))
					que.push(chd);
			}
		}

	for (auto& sloadGraph : disjointChainGraph)
		processSloadGraph(sloadGraph.second, validSloadDoms, runtimeNodes, IDom, reEdges, nodeID2Changes);

	//以下代码仅为统计能够参与优化的SLOAD指令个数占总SLOAD指令的个数
	set<int> affectedSLOADs;
	set<int> allSLOADs;
	for (auto& loc : sloadCFGLocs)
		affectedSLOADs.insert(loc.pc);
	for (auto& instr : instructions)
		if(instr.second == "SLOAD")
			allSLOADs.insert(instr.first);

	cout << "Affected SLOAD " << affectedSLOADs.size() << " " << allSLOADs.size() << endl;

	map<int, set<int>> sloadRelatedBlocks;
	for (auto& nodeID : nodeID2Changes)
		sloadRelatedBlocks[runtimeNodes.at(nodeID.first).getStart()].insert(nodeID.first);
	set<int> sloadPartReIDs;//对应于assertion的相对冗余
	map<int, BlockInstrsChanges*> block2InstrChanges;//对应于assertion的绝对冗余
	for (auto& b : sloadRelatedBlocks) {
		bool same = true;
		auto iter = b.second.begin();
		BlockInstrsChanges* first = nodeID2Changes.at(*iter);
		if (blockNodeIDs.at(b.first).size() > b.second.size())
			same = false;
		else {
			iter++;
			for (; iter != b.second.end(); iter++)
				if (!(*first == *nodeID2Changes.at(*iter))) {
					same = false;
					break;
				}
		}
		if (same)
			block2InstrChanges.insert(make_pair(b.first, first));
		else
			for (auto& id : b.second)
				sloadPartReIDs.insert(id);
	}

	vector<string> stack;
	set<int> pushTags;
	map<int, int> push2JumpMap;
	set<int> JUMPDESTs; genJUMPDESTs(JUMPDESTs);
	set<vector<string>> IDVisited;
	genPushTags(runtimeNodes, 0, stack, getAddrSize(), JUMPDESTs, pushTags, push2JumpMap, IDVisited);

	//与CODECOPY指令相关的offset和size的push地址
	map<int, int> offsetInstrAddrs;
	map<int, int> sizeInstrAddrs;
	map<int, int> codecopyBlocks;
	genCODECOPYOffsetAndSizeInstrs(blocks, codecopyBlocks, offsetInstrAddrs, sizeInstrAddrs);
	//cout << setw(20) << "CODECOPY Addr" << setw(20) << "Block" << setw(20) << "Code Offset Addr" << setw(20) << "Code Size Addr" << endl;
	//for (auto& c : codecopyBlocks) {
	//	string offsetAddr = offsetInstrAddrs.find(c.first) == offsetInstrAddrs.end() ? "/" : to_string(offsetInstrAddrs.at(c.first));
	//	string sizeAddr = sizeInstrAddrs.find(c.first) == sizeInstrAddrs.end() ? "/" : to_string(sizeInstrAddrs.at(c.first));
	//	cout << setw(20) << c.first << setw(20) << c.second << setw(20) << offsetAddr << setw(20) << sizeAddr << endl;
	//}

	z3::context codecopyCtx;
	map<int, vector<expr>> codecopy2OffsetAndSizeExpr = getCODECOPYOffsetAndSizeExpr(blocks, codecopyBlocks, codecopyCtx);
	//for (auto& c : codecopy2OffsetAndSizeExpr) {
	//	cout << "runtime CODECOPY Address : " << c.first << endl;
	//	string start = c.second[0].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[0].to_string().substr(2))) : c.second[0].to_string();
	//	string size = c.second[1].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[1].to_string().substr(2))) : c.second[1].to_string();
	//	cout << "\tcopy start : " << start << endl;
	//	cout << "\tcopy size : " << size << endl;
	//}

	int preCleanRuntimeSize = int(runtime.length()) / 2;//该式成立的前提条件在于runtime为cleanRuntime
	//int preCleanRuntimeSize = instructions.rbegin()->first + getOpcodeSize(instructions.rbegin()->second);
	map<int, int>oldCodecopyAddr2NewOffset;

	//set<int> allReInvAddrs;
	//set<int> invIDs;
	//map<int, int> invRelatedInstrStart;
	//map<int, int> invTypes;

	map<int, string> optimizedInstrs;
	string bytecode;

	optimize(runtimeNodes, edges, blocks, allReInvAddrs, invIDs, IDAddrs, funcEnds, funcTopLevelIDs, instructions, invRelatedInstrStart, invTypes, JUMPDESTs, push2JumpMap, name, optimizedInstrs,
		block2InstrChanges, nodeID2Changes, sloadPartReIDs,
		codecopyBlocks, offsetInstrAddrs, sizeInstrAddrs, preCleanRuntimeSize, oldCodecopyAddr2NewOffset);
	genBytecode(optimizedInstrs, bytecode);

	//测试CODECOPY相关的offset是否改变的正确
	string newRuntime = bytecode + swarmHash;
	string oldRuntime = runtime + swarmHash;
	//这里由于假设copy data的大小不变因此只需要比较offset之后的数据是否相同即可
	//oldCodecopyAddr2NewOffsetAddr不包含offset指令处为CODESIZE的情况
	for (auto& codecopyAddr : oldCodecopyAddr2NewOffset) {
		int newOffset = codecopyAddr.second;
		int oldOffsetAddr = offsetInstrAddrs.at(codecopyAddr.first);
		vector<string> temp;
		boost::split(temp, instructions.at(oldOffsetAddr), boost::is_any_of(" "));
		int oldOffset = -1;
		SSCANF(temp[1].c_str(), "%x", &oldOffset);
		assert(oldRuntime.substr(oldOffset * 2) == newRuntime.substr(newOffset * 2));
	}

	//开始处理deploy instr中的CODECOPY问题
	genInstrs(constructor, deployInstrs);
	genBasicBlocks(deployInstrs, deployBlocks);
	//与CODECOPY指令相关的offset和size的push地址
	map<int, int> deployCodecopyOffsetInstrAddrs;
	map<int, int> deployCodecopySizeInstrAddrs;
	map<int, int> deployCodecopyBlocks;
	genCODECOPYOffsetAndSizeInstrs(deployBlocks, deployCodecopyBlocks, deployCodecopyOffsetInstrAddrs, deployCodecopySizeInstrAddrs);
	codecopy2OffsetAndSizeExpr.clear();
	codecopy2OffsetAndSizeExpr = getCODECOPYOffsetAndSizeExpr(deployBlocks, deployCodecopyBlocks, codecopyCtx);
	//for (auto& c : codecopy2OffsetAndSizeExpr) {
	//	cout << "deploy CODECOPY Address : " << c.first << endl;
	//	string start = c.second[0].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[0].to_string().substr(2))) : c.second[0].to_string();
	//	string size = c.second[1].is_numeral() ? boost::lexical_cast<string>(int256_t("0x" + c.second[1].to_string().substr(2))) : c.second[1].to_string();
	//	cout << "\tcopy start : " << start << endl;
	//	cout << "\tcopy size : " << size << endl;
	//}
	//deploy一般情况下也只需要改动offset
	//只有一种情况需要改动size，就是在最后codecopy runtime的时候，目前我们假设当offset和size均对应于copy runtime的时候才改变size(注意此时不改变offset)
	//其他情况下改动offset

	bool debug = true;
	map<int, int> oldcopyAddr2oldOffset;
	map<int, int> oldcopyAddr2newOffset;
	map<int, int> oldcopyAddr2oldSize;
	map<int, int> oldcopyAddr2newSize;
	for (auto& c : deployCodecopyBlocks) {
		//注意只需要改动size的时候offset应该也存在
		if (deployCodecopyOffsetInstrAddrs.find(c.first) != deployCodecopyOffsetInstrAddrs.end()) {
			int offsetAddr = deployCodecopyOffsetInstrAddrs.at(c.first);
			if (deployInstrs.at(offsetAddr) == "CODESIZE")
				continue;
			vector<string> temp;
			boost::split(temp, deployInstrs.at(offsetAddr), boost::is_any_of(" "));
			int offset = -1;
			SSCANF(temp[1].c_str(), "%x", &offset);
			if (size_t(offset * 2) == constructor.length()) {
				//由于deploy的时候可能有参数的缘故，所以并不一定constructor后的所有指令序列均会被codecopy（最后面可能还有构造函数参数序列）
				//因此size的大小不具备参考性，这里仅用offset的判断条件：offset为runtime的开始位置时默认为copy runtime
				int sizeAddr = deployCodecopySizeInstrAddrs.at(c.first);
				string pushInstr = deployInstrs.at(sizeAddr);
				size_t blankIdx = pushInstr.find(' ');
				string push = pushInstr.substr(0, blankIdx);
				int pushSize = stoi(push.substr(4));
				int pushValue = -1;
				SSCANF(pushInstr.substr(blankIdx + size_t(1)).c_str(), "%x", &pushValue);

				int newValue = int(newRuntime.length() - oldRuntime.length()) / 2 + pushValue;
				stringstream ss;
				ss << hex << newValue;
				string newSize;
				ss >> newSize;
				assert(pushSize * 2 >= newSize.length());
				for (int t = (int)newSize.length(); t < pushSize * 2; t++)
					newSize = "0" + newSize;
				newSize = "0x" + newSize;
				if (debug)
					cout << sizeAddr << " before : " << deployInstrs.at(sizeAddr) << ", after : " << push << " " << newSize << endl;
				deployInstrs.at(sizeAddr) = push + " " + newSize;

				oldcopyAddr2oldOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2newOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2oldSize.insert(make_pair(c.first, pushValue));
				oldcopyAddr2newSize.insert(make_pair(c.first, newValue));
			}
			else {
				int newOffset = int(newRuntime.length() - oldRuntime.length()) / 2 + offset;
				stringstream ss;
				ss << hex << newOffset;
				string newOffsetHexStr;
				ss >> newOffsetHexStr;
				int pushSize = stoi(temp[0].substr(4));
				assert(pushSize * 2 >= newOffsetHexStr.length());
				for (int t = (int)newOffsetHexStr.length(); t < pushSize * 2; t++)
					newOffsetHexStr = "0" + newOffsetHexStr;
				newOffsetHexStr = "0x" + newOffsetHexStr;

				if (debug)
					cout << offsetAddr << " before : " << deployInstrs.at(offsetAddr) << ", after : " << temp[0] << " " << newOffsetHexStr << endl;
				deployInstrs.at(offsetAddr) = temp[0] + " " + newOffsetHexStr;

				oldcopyAddr2oldOffset.insert(make_pair(c.first, offset));
				oldcopyAddr2newOffset.insert(make_pair(c.first, newOffset));
			}
		}
	}
	string newConstructor;
	genBytecode(deployInstrs, newConstructor);
	string newBin = newConstructor + newRuntime;
	string oldBin = constructor + oldRuntime;
	for (auto changedcopy : oldcopyAddr2oldOffset) {
		if (oldcopyAddr2oldSize.find(changedcopy.first) == oldcopyAddr2oldSize.end())
			assert(oldBin.substr(changedcopy.second * 2) == newBin.substr(oldcopyAddr2newOffset.at(changedcopy.first) * 2));
	}

	//solidity编译器的不同版本会导致出现不同的目录分隔符
	char c = '\0';
	if (name.find('/') != string::npos)
		c = '/';
	else {
		assert(name.find('\\') != string::npos);
		c = '\\';
	}
	string contractDir = name.substr(0, name.find_last_of(c) + 1);
	//ofstream optimizeBin(contractDir + getAddress() + ".opevm");
	ofstream optimizeBin(contractDir + ".opsloadevm");
	if (!optimizeBin) {
		cerr << "Fail to open" << (contractDir + getAddress() + ".opsloadevm") << endl;
		exit(-1);
	}
	optimizeBin << bytecode << endl;
	optimizeBin.close();

	ofstream newBinFile(contractDir + newBinFileName);
	newBinFile << newBin << endl;
	newBinFile.close();
}

void Contract::sloadAnalysis(set<int> allReInvAddrs, set<int> invIDs, map<int, int> invRelatedInstrStart, map<int, int> invTypes, string newBinFileName) {
	//ECFGNode::resetCount();
	//genRuntimeByteCFG();
	//if (isRecursive)
	//	return;

	////debugging test
	//for (auto& bb : blocks) {
	//	bool exists = false;
	//	for (auto& n : runtimeNodes)
	//		if (n.second.getStart() == bb.first) {
	//			exists = true;
	//			break;
	//		}
	//	if (!exists) {
	//		cout << "Block " << bb.first << " has not been visited" << endl;
	//	}
	//}

	symExecNodes(runtimeNodes, blocks);
	//testSymStack(runtimeNodes);

	reWriteExpr(runtimeNodes);
	string name = this->name;
	name[name.find_last_of(':')] = '.';
	//genSSAFile(runtimeNodes, name + ".runtime.SSA");
	

	cout << "Starting Redundant SLOAD Analysis" << endl;
	redundantSLOADOptimize(allReInvAddrs, invIDs, invRelatedInstrStart, invTypes, newBinFileName);
}

void Contract::buildVerFront() {
	symExecNodes(runtimeNodes, blocks);
	//testSymStack(runtimeNodes);

	reWriteExpr(runtimeNodes);
	string name = this->name;
	name[name.find_last_of(':')] = '.';
	genSSAFile(runtimeNodes, name + ".runtime.SSA");
}

void Contract::assertAndSloadAnalysis() {
	string name = this->name;
	name[name.find_last_of(':')] = '.';
	//replace(name.begin(), name.end(), ':', '.');
	//generateDisasm(instructions, name + ".runtime");
	//genSrcMapFile(srcmapRuntime, instructions, name + ".srcmap");

	map<int, set<int>> edges;
	pruningInvalids(runtimeNodes, edges);
	//generateInvalidDotGraph(runtimeNodes, name + ".dot", edges);
	
	set<int> invIDs;
	set<int> invAddrs;
	map<int, set<int>> invAddr2IDs;//不需要进行后续传参
	map<int, int> invRelatedInstrStart;
	map<int, int> invTypes;
	//invAddrs, invIDs, invRelatedInstrStart, invTypes
	if (edges.empty()) {
		cout << "NoInvalid" << endl;
	}
	else {

		//jmpiTgt和natTgt均是block 开始地址，不是Node ID
		set<int> jmpiTgt; getJumpITgt(blocks, jmpiTgt);
		set<int> natTgt; getNaturalTgt(blocks, natTgt);

		vector<int> redundantInvs;//所有冗余的INVALID Node ID
		set<int> loopInvalids;

		parallelSolve(edges, runtimeNodes, jmpiTgt, natTgt, loopInvalids, redundantInvs);

		cout << "Constraint solving ends" << endl;

		for (auto& i : redundantInvs) {
			invAddrs.insert(runtimeNodes.at(i).getStart());
			invIDs.insert(i);
			invAddr2IDs[runtimeNodes.at(i).getStart()].insert(i);
		}


		invRelatedInstrStart =
			getInvRelatedInstrsStart(invAddrs, edges, runtimeNodes, jmpiTgt, natTgt);
		//对于未计算出冗余相关指令序列的INVALID进行除名
		for (auto iter = invAddrs.begin(); iter != invAddrs.end();) {
			if (invRelatedInstrStart.find(*iter) == invRelatedInstrStart.end()) {
				int invAddr = *iter;
				iter = invAddrs.erase(iter);
				for (auto& id : invAddr2IDs.at(invAddr))
					invIDs.erase(id);
				invAddr2IDs.at(invAddr).clear();
			}
			else
				iter++;
		}

		bool redundancy = false;
		for (auto& inv : invAddr2IDs)
			if (!inv.second.empty()) {
				redundancy = true;
				break;
			}
		if (!redundancy)
			cout << "NoRedundantInvalid" << endl;
		else {
			auto invBegin = invIDs.begin();
			cout << *invBegin;
			invBegin++;
			while (invBegin != invIDs.end()) {
				cout << "," << *invBegin;
				invBegin++;
			}
			cout << endl;

			set<int> allInvalidAddrs;
			set<int> allNonLoopInvalidAddrs;
			set<int> affectedInvalidAddrs;
			for (auto& i : invIDs)
				affectedInvalidAddrs.insert(runtimeNodes.at(i).getStart());
			for (auto& i : runtimeNodes)
				if (i.second.getBlockType() == BlockType::INVALID) {
					allInvalidAddrs.insert(i.second.getStart());
					if (loopInvalids.find(i.first) == loopInvalids.end())
						allNonLoopInvalidAddrs.insert(i.second.getStart());
				}
			cout << "Affected Assertion " << affectedInvalidAddrs.size() << " " << allNonLoopInvalidAddrs.size() << " " << allInvalidAddrs.size() << endl;
		}

		//map<int, int> invTypes;
		//type == 1 表明为正常INVALID
		//type == 2 表明不能删除JUMPDEST
		//在判断inv type == 2时需要判断JUMP地址是否在type == 1的冗余序列中
		//示例由2513、3235和4052三个invalid地址的上一个push 的地址为2514，这时虽然2513 type == 1但是2514还是不能删，应该将2513的type改为2
		//可能还有后续...

		set<int> reservedJUMPDESTs;
		for (auto& inv : invRelatedInstrStart) {
			auto invIter = instructions.find(inv.first);
			invIter--;
			string jumpi = invIter->second; assert(jumpi == "JUMPI"); invIter--;
			string pushAddr = invIter->second; assert(pushAddr.find("PUSH" + to_string(getAddrSize())) != string::npos);
			vector<string> temp;
			boost::split(temp, pushAddr, boost::is_any_of(" "));
			int tagAddr = -1;
			SSCANF(temp[1].c_str(), "%x", &tagAddr);
			if (tagAddr == inv.first + 1)//可以顺序删除INVALID指令下的JUMPDEST指令
				invTypes.insert(make_pair(inv.first, 1));
			else {
				reservedJUMPDESTs.insert(tagAddr);
				invTypes.insert(make_pair(inv.first, 2));
			}
		}

		//即使定位到的冗余序列是连续的，也不一定能完全删除
		//示例如下：
		//3128 : DUP2
		//3129 : ISZERO
		//3130 : ISZERO
		//3131 : PUSH2 0x0ae3
		//3134 : JUMPI
		//3135 : INVALID
		//3136 : JUMPDEST
		//以上为3135处assertion的冗余序列，可以看到3131处 push的地址并不是INVALID的下一条地址，相反3136还有其他地方需要其跳转
		//所以以上可删的部分为3128、3129、3130，3135并且将3134处的JUMPI指令改为JUMP


		for (auto& bb : blockNodeIDs)
			if (blocks.at(bb.first).getJumpType() == BlockType::INVALID) {
				size_t allIDNum = bb.second.size();
				size_t partReNum = 0;
				if (invAddr2IDs.find(bb.first) != invAddr2IDs.end())
					partReNum = invAddr2IDs.at(bb.first).size();
				cout << bb.first << "\t" << allIDNum << "\t" << partReNum << endl;
			}

		//cout << invRelatedInstrStart.size() << endl;
		//for (auto& id : redundantInvs) {
		//	int addr = runtimeNodes.at(id).getStart();
		//	cout << id << "\t" << addr << "\t" << invRelatedInstrStart.at(addr) << endl;
		//}

		vector<string> stack;
		set<int> pushTags;
		map<int, int> push2JumpMap;
		set<int> JUMPDESTs; genJUMPDESTs(JUMPDESTs);
		set<vector<string>> IDVisited;
		genPushTags(runtimeNodes, 0, stack, getAddrSize(), JUMPDESTs, pushTags, push2JumpMap, IDVisited);

		map<int, set<int>> addr2PushTags;//存储JUMPDEST地址 => 所有push该地址的指令地址
		for (auto& i : pushTags) {
			string opcode = instructions.find(i)->second;
			vector<string> temp;
			boost::split(temp, opcode, boost::is_any_of(" "));
			int destAddr = -1;
			SSCANF(temp[1].c_str(), "%x", &destAddr);
			addr2PushTags[destAddr].insert(i);
		}
		for (auto& inv : invTypes) {
			if (inv.second == 1)
				if (reservedJUMPDESTs.find(inv.first + 1) != reservedJUMPDESTs.end())
					inv.second = 2;
				else if (addr2PushTags.at(inv.first + 1).size() > 1)//冗余序列之外还有其他地方跳转到INVALID之后的JUMPDEST
					inv.second = 2;
		}
	}
	//invRelatedInstrStart和invTypes的key值均为INVALID地址
	sloadAnalysis(invAddrs, invIDs, invRelatedInstrStart, invTypes, "newAssertAndSloadBin");
}