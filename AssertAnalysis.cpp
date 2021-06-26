#include "Contract.h"
#include <list>
#include <queue>
using z3::expr;

void displayStack(const vector<expr>& stack) {
	int i = 0;
	for (auto it = stack.rbegin(); it != stack.rend(); it++, i++)
		if ((*it).is_numeral())
			cout << i << " : " << (*it).get_decimal_string(256) << endl;
		else
			cout << i << " : " << (*it).to_string() << endl;
}
void displayMemory(const map<string, expr>& memory) {
	displayYellowMsg("=================");
	for (auto& m : memory)
		cout << m.first << " : " << m.second << endl;
	displayYellowMsg("=================");
}

void displayStorage(const map<string, expr>& storage) {
	displayBlueMsg("==================");
	for (auto& s : storage)
		cout << s.first << " : " << s.second << endl;
	displayBlueMsg("==================");
}

//static z3::context globalCtx;
z3::expr* returnDataSize = NULL;
string getExprString(const expr& e) {
	if (e.is_numeral())
		return e.get_decimal_string(256);
	else
		return e.to_string();
}
void processReturnData(const expr& out, const expr& outSize, map<string, expr>& memory) {
	string outStart = out.is_numeral() ? out.get_decimal_string(256) : out.to_string();
	expr end = (out + outSize).simplify();
	string outEnd = end.is_numeral() ? end.get_decimal_string(256) : end.to_string();
	string size = outSize.is_numeral() ? outSize.get_decimal_string(256) : outSize.to_string();
	//由于函数return需要修改调用者的memory，只需要删除有影响的memory content即可
	assert(outSize.is_numeral());
	if (size != "0") {
		for (auto iter = memory.begin(); iter != memory.end();) {
			size_t dollarIdx = iter->first.find_first_of('$');
			string memStart = iter->first.substr(0, dollarIdx);
			if (memStart == outStart)
				iter = memory.erase(iter);
			//memStart is numerical means memEnd is numerical too.
			else if (isNumerical(memStart) && isNumerical(outStart)) {
				string memEnd = iter->first.substr(dollarIdx + 1);
				int mem1 = atoi(memStart.c_str());
				int mem2 = atoi(memEnd.c_str());
				int out1 = atoi(outStart.c_str());
				int out2 = out1 + atoi(size.c_str());
				if ((mem1 <= out1 && out1 < mem2) || (mem1 < out2 && out2 <= mem2))
					iter = memory.erase(iter);
				else
					iter++;
			}
			else
				iter++;
		}
	}

	static int returnNum = 0;
	int returnSize = atoi(size.c_str());
	expr s = out;
	for (int i = 0; i < returnSize; i += 32) {
		int segSize = 0;
		if (i + 32 > returnSize)
			segSize = returnSize - i;
		else
			segSize = 32;
		expr e = (s + segSize).simplify();
		string loc = getExprString(s) + "$" + getExprString(e);
		string returnData = "return_" + to_string(returnNum) + "#" + to_string(i) + "$" + to_string(i + segSize);
		memory.insert(make_pair(loc, outSize.ctx().bv_const(returnData.c_str(), 256)));
		s = e;
	}
	returnNum++;
	if (returnDataSize == NULL)
		returnDataSize = new expr(outSize);
	else {
		//cout << "returnDataSize : " << (*returnDataSize) << endl;
		delete returnDataSize;
		returnDataSize = new expr(outSize);
	}
}

void symExecInstr(int pc, string instr, z3::context& c, vector<z3::expr>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, expr& jumpiCond) {
	vector<string> instrParts;
	boost::split(instrParts, instr, boost::is_any_of(" "));
	string mnemonic = instrParts[0];
	int opcode = Opcode::getOpcode(mnemonic);
	size_t top = stack.size() - 1;
	if (stack.size() < (size_t)get<0>(Opcode::getOperation(opcode)))
		throw ("Insufficient operands : " + to_string(pc) + " " + instr);
	
	bool debug = false;
	if (debug) {
		displayRedMsg("before symbolic execute " + to_string(pc) + instr);
		for (size_t i = 0; i < stack.size(); i++)
			cout << i << " " << stack[i].to_string() << endl;
	}

	static int callNum = 0;
	static int createNum = 0;
	switch (opcode) {
	case 0x00://STOP
		break;
	case 0x01: {//ADD
		assert(!stack[top].is_bool() && !(stack[top - 1].is_bool()));
		stack[top - 1] = (stack[top] + stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x02: {//MUL
		//assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		if (stack.at(top).is_bool())
			stack[top] = z3::ite(stack[top], c.bv_val(1, 256), c.bv_val(0, 256));
		if (stack[top - 1].is_bool())
			stack[top - 1] = z3::ite(stack[top - 1], c.bv_val(1, 256), c.bv_val(0, 256));
		stack[top - 1] = (stack[top] * stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x03: {//SUB
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		stack[top - 1] = (stack[top] - stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x04: {//DIV
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		stack[top - 1] = z3::udiv(stack[top], stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x05: {//SDIV
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		stack[top - 1] = (stack[top] / stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x06: {//MOD
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		stack[top - 1] = z3::ite(stack[top - 1] == 0, c.bv_val(0, 256), z3::urem(stack[top], stack[top - 1])).simplify();
		stack.pop_back();
		break;
	}
	case 0x07: {//SMOD
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		stack[top - 1] = z3::ite(stack[top - 1] == 0, c.bv_val(0, 256), z3::urem(z3::ite(stack[top] < 0, -stack[top], stack[top]), z3::ite(stack[top - 1] < 0, -stack[top - 1], stack[top - 1]))).simplify();
		stack.pop_back();
		break;
	}
	case 0x08: {//ADDMOD
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()) && !(stack.at(top - 2).is_bool()));
		expr zero = c.bv_val(0, 1);
		if (stack[top - 2].is_numeral() && stack[top - 2].get_decimal_string(256) == "0")
			stack[top - 2] = zero;
		else {
			z3::expr x = z3::concat(zero, stack[top]);
			z3::expr y = z3::concat(zero, stack[top - 1]);
			z3::expr z = z3::concat(zero, stack[top - 2]);
			stack[top - 2] = z3::ite(stack[top - 2] == 0, c.bv_val(0, 256), z3::urem(x + y, z).extract(255, 0)).simplify();
		}
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x09: {//MULMOD
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()) && !(stack.at(top - 2).is_bool()));
		expr zero = c.bv_val(0, 256);
		if (stack[top - 2].is_numeral() && stack[top - 2].get_decimal_string(256) == "0")
			stack[top - 2] = zero;
		else {
			z3::expr x = z3::concat(zero, stack[top]);
			z3::expr y = z3::concat(zero, stack[top - 1]);
			z3::expr z = z3::concat(zero, stack[top - 2]);
			stack[top - 2] = z3::ite(stack[top - 2] == 0, c.bv_val(0, 256), z3::urem(x * y, z).extract(255, 0)).simplify();
		}
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x0a: {//EXP
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		if (stack[top - 1].is_numeral() && stack[top].is_numeral()) {
			//cout << "base : " << stack[top].to_string() << endl;
			//cout << "exponent : " << stack[top - 1].to_string() << endl;

			//指数可能为比较大的无符号数，不足以用uint32来表示，只能先用uint256表示，再转换为uint32，虽然有数据损失，但指数过大时本就计算不精确，所以损失高位数据可行
			//stack[top - 1] = c.bv_val(boost::multiprecision::pow(uint256_t(stack[top].get_decimal_string(256)), stack[top - 1].get_numeral_uint()).str().c_str(), 256);
			stack[top - 1] = c.bv_val(boost::multiprecision::pow(uint256_t(stack[top].get_decimal_string(256)), uint256_t(stack[top - 1].get_decimal_string(256)).convert_to<unsigned int>()).str().c_str(), 256);
			//cout << "result : " << stack[top - 1].to_string() << endl;
		}
		else {
			stack[top - 1] = c.bv_const(("exp#" + stack[top].to_string() + "#" + stack[top - 1].to_string()).c_str(), 256);
		}
		stack.pop_back();
		break;
	}
	case 0x0b: {//SIGNEXTEND
		assert(!stack.at(top).is_bool() && !(stack.at(top - 1).is_bool()));
		if (stack[top].is_numeral() && stack[top - 1].is_numeral()) {
			int256_t first = int256_t(stack.at(top).get_decimal_string(256));
			if (first >= 32 || first <= 0) {/*second remains unchanged*/ }
			else {
				int256_t second = int256_t(stack.at(top - 1).get_decimal_string(256));
				unsigned int signedBitsFromRight = (8 * first + 7).convert_to<unsigned int>();
				int256_t flag = ((int256_t)1) << signedBitsFromRight;
				int256_t sign = flag & second;
				if (sign == 0) {//signed_bit = 0,mask  000...01...111 
					int256_t mask = flag - 1;
					stack[top - 1] = c.bv_val((mask & second).str().c_str(), 256);
				}
				else {//mask 111...10...000
					int256_t mask = ~(flag - 1);
					stack[top - 1] = c.bv_val((mask | second).str().c_str(), 256);
				}
			}
		}
		else {
			string signextend = "signextend#" + stack[top].to_string() + "#" + stack[top - 1].to_string();
			stack[top - 1] = c.bv_const(signextend.c_str(), 256);
		}
		stack.pop_back();
		break;
	}


			 //Comparison & Bitwise Logic Operations
	case 0x10: {//LT
		stack[top - 1] = z3::ult(stack[top], stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x11: {//GT
		stack[top - 1] = z3::ugt(stack[top], stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x12: {//SLT
		stack[top - 1] = (stack[top] < stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x13: {//SGT
		stack[top - 1] = (stack[top] > stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x14: {//EQ
		//存在常数1(bv)与bool expr的比较
		if ((stack[top].is_bv() && stack[top - 1].is_bv()) || (stack[top].is_bool() && stack[top - 1].is_bool()))
			stack[top - 1] = (stack[top] == stack[top - 1]).simplify();
		else {
			expr bvExper(c);
			expr other(c);
			if (stack[top - 1].is_bool()) {
				bvExper = z3::ite(stack[top - 1], c.bv_val(1, 256), c.bv_val(0, 256));
				other = stack[top];
			}
			else {
				bvExper = z3::ite(stack[top], c.bv_val(1, 256), c.bv_val(0, 256));
				other = stack[top - 1];
			}
			stack[top - 1] = (bvExper == other).simplify();
		}
		stack.pop_back();
		break;
	}
	case 0x15: {//ISZERO
		//ISZERO能作用于bool expr和bv expr
		//ISZERO指令会检测 call value是否为0，因此能够作用于bv expr
		//ISZERO指令的结果应该是bool expr
		if (stack[top].is_bool())
			stack[top] = (!stack[top]).simplify();
		else {
			//assert(stack[top].is_numeral() && (stack[0].get_numeral_int() == 0 || stack[0].get_numeral_int() == 1));
			//stack[top] = z3::ite(stack[top] == 0, c.bv_val(1, 256), c.bv_val(0, 256)).simplify();
			stack[top] = (stack[top] == 0).simplify();
		}
		break;
	}
			 //solidity对于逻辑表达式是短路处理的，并不会用到AND,OR,XOR,NOT指令
	case 0x16: {//AND
		//0x97f75ac00a32d54b7fd3a3cf156343cdcb5060f9出现31283处的AND指令处理的为bool值
		assert((stack[top].is_bv() && stack[top - 1].is_bv()) || (stack[top].is_bool() && stack[top - 1].is_bool()));
		if (stack[top].is_bool())
			stack[top - 1] = (stack[top] && stack[top - 1]).simplify();
		else
			stack[top - 1] = (stack[top] & stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x17: {//OR
		//assert((stack[top].is_bv() && stack[top - 1].is_bv()) || (stack[top].is_bool() && stack[top - 1].is_bool()));
		if (stack[top].is_bv() && stack[top - 1].is_bv())
			stack[top - 1] = (stack[top] | stack[top - 1]).simplify();
		else if(stack[top].is_bool() && stack[top - 1].is_bool())
			stack[top - 1] = (stack[top] || stack[top - 1]).simplify();
		else if(stack[top].is_bv() && stack[top - 1].is_bool())
			stack[top - 1] = (stack[top] | z3::ite(stack[top - 1], c.bv_val(1, 256), c.bv_val(0, 256))).simplify();
		else
			stack[top - 1] = (stack[top - 1] | z3::ite(stack[top], c.bv_val(1, 256), c.bv_val(0, 256))).simplify();
		stack.pop_back();
		break;
	}
	case 0x18: {//XOR
		assert(stack[top].is_bv() && stack[top - 1].is_bv());
		stack[top - 1] = (stack[top] ^ stack[top - 1]).simplify();
		stack.pop_back();
		break;
	}
	case 0x19: {//NOT
		stack[top] = (~stack[top]).simplify();
		break;
	}
	case 0x1a: {//BYTE
		stack[top - 1] = (stack[top - 1] & z3::shl(c.bv_val(0xff, 256), stack[top] * 8)).simplify();
		stack.pop_back();
		break;
	}
	case 0x1b: {//SHL
		stack[top - 1] = z3::shl(stack[top - 1], stack[top]).simplify();
		stack.pop_back();
		break;
	}
	case 0x1c: {//SHR
		stack[top - 1] = z3::lshr(stack[top - 1], stack[top]).simplify();
		stack.pop_back();
		break;
	}
	case 0x1d: {//SAR
		stack[top - 1] = z3::ashr(stack[top - 1], stack[top]).simplify();
		stack.pop_back();
		break;
	}


			 //SHA3
	case 0x20: {//SHA
		static int sha3Num = 0;
		if (stack[top - 1].is_numeral() && stack[top - 1].get_numeral_int() != 0) {//size is numeral
			int offInt = stack[top].is_numeral() ? stack[top].get_numeral_int() : -1;
			int size = stack[top - 1].get_numeral_int();//0x4021d8382da2a268ffe39dbbc36c97b31e5461c4的10104处的SHA3会出现size为0的异常情况
			expr content = c.bv_val(0, 1);
			int i;
			for (i = 0; i < size; i += 32) {
				string memLoc;
				int end = 0;
				//size可能不是32的整数倍，比如28
				if (i + 32 > size)
					end = size;
				else
					end = i + 32;
				if (stack[top].is_numeral())
					memLoc = to_string(offInt + i) + "$" + to_string(offInt + end);
				else
					memLoc = (stack[top] + i).simplify().to_string() + "$" + (stack[top] + end).simplify().to_string();
				//size可能不是32的整数倍，比如28
				expr mem(c);
				if (memory.find(memLoc) == memory.end())
					mem = c.bv_const(("mem_" + memLoc).c_str(), 256);
				else
					mem = memory.at(memLoc);
				content = z3::concat(content, mem);
			}
			//位向量右边为低位
			content = content.extract(i * 8 - 1, i * 8 - size * 8).simplify();
			stack[top - 1] = c.bv_const(("sha3#" + content.to_string()).c_str(), 256);
			//stack[top - 1] = c.bv_const(("sha3" + bytes).c_str(), 256);
		}
		else {//一般见于对string类型的keccak操作
			stack[top - 1] = c.bv_const(("sha3_" + to_string(sha3Num)).c_str(), 256);
			sha3Num++;
		}
		stack.pop_back();
		break;
	}

	case 0x30: {//ADDRESS
		stack.push_back(c.bv_const("Ia", 256));
		break;
	}
	case 0x31: {//BALANCE
		stack[top] = c.bv_const(("balance#" + stack[top].to_string()).c_str(), 256);
		break;
	}
	case 0x32: {//ORIGIN
		stack.push_back(c.bv_const("Io", 256));
		break;
	}
	case 0x33: {//CALLER
		stack.push_back(c.bv_const("Is", 256));
		break;
	}
	case 0x34: {//CALLVALUE
		stack.push_back(c.bv_const("Iv", 256));
		break;
	}
	case 0x35: {//CALLDATALOAD
		if (stack[top].is_numeral())
			stack[top] = c.bv_const(("Id_" + stack[top].get_decimal_string(256)).c_str(), 256);
		else
			stack[top] = c.bv_const(("Id_" + stack[top].to_string()).c_str(), 256);
		break;
	}
	case 0x36: {//CALLDATASIZE
		stack.push_back(c.bv_const("Id_size", 256));
		break;
	}
	case 0x37: {//CALLDATACOPY

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x38: {//CODESIZE
		stack.push_back(c.bv_const("Id_size", 256));
		break;
	}
	case 0x39: {//CODECOPY
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x3a: {//GASPRICE
		stack.push_back(c.bv_const("Ip", 256));
		break;
	}
	case 0x3b: {//EXTCODESIZE
		stack[top] = c.bv_const(("Ib_szie#" + stack[top].to_string()).c_str(), 256);
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
		stack.push_back(*returnDataSize);
		break;
	}
	case 0x3e: {//RETURNDATACOPY
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x3f: {//EXTCODEHASH(君士坦丁堡版本新增指令)
		stack[top] = c.bv_const(("Ib_codehash#" + stack[top].to_string()).c_str(), 256);
	}

	case 0x40: {//BLOCKHASH
		stack[top] = c.bv_const(("IH_p#" + stack[top].to_string()).c_str(), 256);
		break;
	}
	case 0x41: {//COINBASE
		stack.push_back(c.bv_const("IH_c", 256));
		break;
	}
	case 0x42: {//TIMESTAMP
		stack.push_back(c.bv_const("IH_s", 256));
		break;
	}
	case 0x43: {//NUMBER
		stack.push_back(c.bv_const("IH_i", 256));
		break;
	}
	case 0x44: {//DIFFICULTY
		stack.push_back(c.bv_const("IH_d", 256));
		break;
	}
	case 0x45: {//GASLIMIT
		stack.push_back(c.bv_const("IH_l", 256));
		break;
	}
	case 0x46: {//CHAINID
		stack.push_back(c.bv_const("chainID", 256));
		break;
	}
	case 0x47: {//SELFBALANCE
		stack.push_back(c.bv_const("balance#Ia", 256));
		break;
	}


	case 0x50: {//POP
		stack.pop_back();
		break;
	}
	case 0x51: {//MLOAD
		string start = stack[top].is_numeral() ? stack[top].get_decimal_string(256) : stack[top].to_string();
		expr memEnd = (stack[top] + 32).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();
		string loc = start + "$" + end;
		if (memory.find(loc) != memory.end())
			stack[top] = memory.at(loc);
		else {
			stack[top] = c.bv_const(("mem_" + loc).c_str(), 256);
		}
		//cout << pc << " MLOAD : " << "location " << loc << ", value " << stack[top].to_string() << endl;
		//displayMemory(memory);
		break;
	}
	case 0x52: {//MSTORE
		string start = stack[top].is_numeral() ? stack[top].get_decimal_string(256) : stack[top].to_string();
		expr memEnd = (stack[top] + 32).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();
		string loc = start + "$" + end;

		//memory[] : the lack of default constructor of z3::expr
		//memory.insert(key, value) or memory.emplace(key, value) can't insert when key already exists
		expr store = stack[top - 1].is_bool() ? z3::ite(stack[top - 1], c.bv_val(1, 256), c.bv_val(0, 256)).simplify() : stack[top - 1];
		auto iter = memory.find(loc);
		if (iter == memory.end())
			memory.emplace(make_pair(loc, store));
		else
			iter->second = store;
		//cout << pc << "MSTORE : " << "location " << loc << ", value " << stack[top - 1].to_string() << endl;
		stack.pop_back();
		stack.pop_back();

		//displayMemory(memory);
		break;
	}
	case 0x53: {//MSTORE8
		string start = stack[top].is_numeral() ? stack[top].get_decimal_string(256) : stack[top].to_string();
		expr memEnd = (stack[top] + 8).simplify();
		string end = memEnd.is_numeral() ? memEnd.get_decimal_string(256) : memEnd.to_string();
		//expr wordEnd = stack[top] + 32;
		//string word = wordEnd.is_numeral() ? wordEnd.get_decimal_string(256) : wordEnd.to_string();

		string loc = start + "$" + end;
		//string wordLoc = start + "$" + word;
		//memory.emplace(make_pair(loc, stack[top - 1]));

		auto iter = memory.find(loc);
		if (iter == memory.end())
			memory.emplace(make_pair(loc, (stack[top - 1] & c.bv_val(0xff, 256)).simplify()));
		else {
			iter->second = (stack[top - 1] & c.bv_val(0xff, 256)).simplify();
		}

		stack.pop_back();
		stack.pop_back();

		//displayMemory(memory);
		break;
	}
	case 0x54: {//SLOAD
		string loc = stack[top].is_numeral() ? stack[top].get_decimal_string(256) : stack[top].to_string();
		if (storage.find(loc) != storage.end())
			stack[top] = storage.at(loc);
		else
			stack[top] = c.bv_const(("st_" + loc).c_str(), 256);

		//displayStorage(storage);
		break;
	}
	case 0x55: {//SSTORE
		string loc = stack[top].is_numeral() ? stack[top].get_decimal_string(256) : stack[top].to_string();
		auto iter = storage.find(loc);
		if (iter == storage.end())
			storage.emplace(make_pair(loc, stack[top - 1]));
		else
			iter->second = stack[top - 1];

		stack.pop_back();
		stack.pop_back();

		//displayStorage(storage);
		break;
	}
	case 0x56: {//JUMP

		//JUMP target info has already stored in CFG
		stack.pop_back();
		break;
	}
	case 0x57: {//JUMPI
		if (stack[top - 1].is_bv()) {
			//cout << "JUMP Condition(not bool) : " << stack[top - 1] << endl;
			jumpiCond = (stack[top - 1] != 0).simplify();
		}
		else {
			assert(jumpiCond.is_bool());
			jumpiCond = stack[top - 1];
		}
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0x58: {//PC
		stack.push_back(c.bv_val(pc, 256));
		break;
	}
	case 0x59: {//MSIZE
		static int msizeCnt = 0;
		string name = "msize_" + to_string(msizeCnt);
		stack.push_back(c.bv_const(name.c_str(), 256));
		msizeCnt++;
		break;
	}
	case 0x5a: {//GAS
		static int gasCnt = 0;
		string name = "gas_" + to_string(gasCnt);
		stack.push_back(c.bv_const(name.c_str(), 256));
		gasCnt++;
		break;
	}
	case 0x5b: {//JUMPDEST
		break;
	}
	case 0x60:case 0x61:case 0x62:case 0x63:case 0x64:case 0x65:case 0x66:case 0x67:case 0x68:case 0x69:case 0x6a:case 0x6b:case 0x6c:case 0x6d:case 0x6e:case 0x6f:
	case 0x70:case 0x71:case 0x72:case 0x73:case 0x74:case 0x75:case 0x76:case 0x77:case 0x78:case 0x79:case 0x7a:case 0x7b:case 0x7c:case 0x7d:case 0x7e:case 0x7f: {
		//PUSHx

		string value = instrParts[1];
		if (Contract::isHex(value.substr(2))) {
			uint256_t pushValue(instrParts[1]);
			string value = boost::lexical_cast<string>(pushValue);
			stack.push_back(c.bv_val(value.c_str(), 256));
		}
		else {//PUSH20 0x__$a8e7faaf74260e17257bd0c7c0f0ee1665$__
			static map<string, int> libAddrMap;
			static int libNum = 0;
			auto iter = libAddrMap.find(instrParts[1]);
			if (iter == libAddrMap.end()) {
				libAddrMap.insert(pair<string, int>(instrParts[1], libNum));
				stack.push_back(c.bv_const(("lib_" + to_string(libNum)).c_str(), 256));
				libNum++;
			}
			else
				stack.push_back(c.bv_const(("lib_" + to_string(iter->second)).c_str(), 256));
		}
		break;
	}
	case 0x80:case 0x81:case 0x82:case 0x83:case 0x84:case 0x85:case 0x86:case 0x87:case 0x88:case 0x89:case 0x8a:case 0x8b:case 0x8c:case 0x8d:case 0x8e:case 0x8f: {
		//DUPx
		size_t loc = top - (opcode - 0x80);
		stack.push_back(stack[loc]);
		break;
	}
	case 0x90:case 0x91:case 0x92:case 0x93:case 0x94:case 0x95:case 0x96:case 0x97:case 0x98:case 0x99:case 0x9a:case 0x9b:case 0x9c:case 0x9d:case 0x9e:case 0x9f: {
		//SWAPx
		size_t loc = top - (opcode - 0x90 + 1);
		z3::expr temp = stack[top];
		stack[top] = stack[loc];
		stack[loc] = temp;
		break;
	}


	case 0xa0:case 0xa1:case 0xa2:case 0xa3:case 0xa4: {
		//LOGx
		stack.pop_back();
		stack.pop_back();
		for (int i = 0xa0; i < opcode; i++)
			stack.pop_back();
		break;
	}

			 //在符号执行过程中message call类指令的返回状态应该用bool符号值表示，而不能用true表示
			 //CREATE和CREATE2指令的返回值为新创建的合约地址，因此为bv
	case 0xf0: {
		//CREATE
		//operand order : value, input offset, input size
		expr outSize = c.bv_val(0, 256);
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
		stack.push_back(c.bv_const(("create" + to_string(createNum)).c_str(), 256));
		createNum++;
		break;
	}
	case 0xf1: {
		//CALL
		//operand order : gas, to, value, in offset, in size, out offset, out size
		processReturnData(stack[top - 5], stack[top - 6], memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(c.bool_const(("call" + to_string(callNum)).c_str()));
		callNum++;

		//displayMemory(memory);
		break;
	}
	case 0xf2: {//CALLLCODE
		//operand order : gas, to, value, in offset, in size, out offset, out size
		//use caller's storage
		processReturnData(stack[top - 5], stack[top - 6], memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(c.bool_const(("call" + to_string(callNum)).c_str()));
		callNum++;

		//displayMemory(memory);
		break;
	}
	case 0xf3: {//RETURN
		//目前不分析合约间的跳转关系，因此RETURN指令暂时不用处理
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0xf4: {//DELEGATECALL
		//operand order : gas, to, in offset, in size, out offset, out size
		processReturnData(stack[top - 4], stack[top - 5], memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(c.bool_const(("call" + to_string(callNum)).c_str()));
		callNum++;

		//displayMemory(memory);
		break;
	}
	case 0xf5: {
		//CREATE2
		//operand order : endowment, memory_start, memory_length, salt

		expr outSize = c.bv_val(0, 256);
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
		stack.push_back(c.bv_const(("create" + to_string(createNum)).c_str(), 256));
		createNum++;
		break;
	}
	case 0xfa: {//STATICCALL
	//operand order : gas, to, in offset, in size, out offset, out size
		processReturnData(stack[top - 4], stack[top - 5], memory);

		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(c.bool_const(("call" + to_string(callNum)).c_str()));
		callNum++;

		//displayMemory(memory);
		break;
	}
	case 0xfd: {//REVERT
		stack.pop_back();
		stack.pop_back();
		break;
	}
	case 0xfe: {//INVALID
		break;
	}
	case 0xff: {//SELFDESTRUCT
		stack.pop_back();
		break;
	}
	}
}

void pruningInvalid(const map<int, ECFGNode>& nodes, int invID, map<int, set<int>>& edges) {
	map<int, set<int>> reverseEdges;
	for (auto& n : nodes)
		for (auto& pnt : n.second.getParents())
			if (pnt != -1)
				reverseEdges[n.first].insert(pnt);

	map<int, set<int>> reverseInvEdges;
	list<int> que;
	set<int> visited;
	que.push_back(invID);
	while (!que.empty()) {
		int i = que.front();
		visited.insert(i);
		que.pop_front();

		if (reverseEdges.find(i) == reverseEdges.end())
			continue;

		for (auto j : reverseEdges.at(i)) {
			if (visited.find(j) == visited.end())
				que.push_back(j);
			reverseInvEdges[i].insert(j);
		}
	}

	for (auto& es : reverseInvEdges) {
		if (edges.find(es.first) == edges.end())
			edges[es.first] = { };
		for (auto& e : es.second)
			edges[e].insert(es.first);
	}
}

void pruningInvalids(const map<int, ECFGNode>& nodes, map<int, set<int>>& edges) {
	vector<int> invalids;

	map<int, set<int>> reverseEdges;
	for (auto& n : nodes) {
		if (n.second.getBlockType() == BlockType::INVALID)
			invalids.push_back(n.first);
		for (auto& pnt : n.second.getParents())
			if (pnt != -1)
				reverseEdges[n.first].insert(pnt);
	}

	map<int, set<int>> reverseInvEdges;
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
				reverseInvEdges[i].insert(j);
			}
		}
	}

	for (auto& es : reverseInvEdges) {

		//invalid nodes has no edges
		if (edges.find(es.first) == edges.end())
			edges[es.first] = { };

		for (auto& e : es.second)
			edges[e].insert(es.first);
	}
}

map<int, int> genIDom(const map<int, set<int>>& graph) {
	//Step 1 : calculate a sort of reverse post order traversal
	map<int, set<int>> parents;//NodeID => parent node set
	for (auto& g : graph) {
		parents[g.first] = {};
	}
	for (auto& g : graph) {
		for (auto& child : g.second)
			parents[child].insert(g.first);
	}

	map<int, bool> visited;//NodeID => isVisited
	for (auto& g : graph)
		visited[g.first] = false;


	list<int> s; s.push_back(graph.begin()->first);
	visited[graph.begin()->first] = true;

	map<int, int> PO;//postorder traversal(NodeID => po)
	int count = 0;
	while (!s.empty()) {
		int visit = s.back();
		bool isEnd = true;
		for (auto& child : graph.at(visit)) {
			if (!visited[child]) {
				visited[child] = true;
				s.push_back(child);
				isEnd = false;
			}
		}
		if (isEnd) {
			s.pop_back();
			PO[visit] = count;
			count++;
		}
	}

	map<int, int> RPO;//reverse postorder traversal(rpo => NodeID)
	for (auto i : PO)
		RPO[int(graph.size()) - 1 - i.second] = i.first;

	//Step 2 : calculate IDom
	map<int, int> IDom;
	for (auto& g : graph)
		IDom[g.first] = -1;
	IDom[graph.begin()->first] = graph.begin()->first;
	bool changed = true;
	map<int, int> idOrder;
	for (auto& i : RPO)
		idOrder[i.second] = i.first;

	while (changed) {
		changed = false;
		for (auto order : RPO) {//RPO : order => NodeID
			if (order.second == graph.begin()->first)
				continue;
			int ID = order.second;

			//寻找ID的第一个前驱，即RPO中最靠前的前驱
			auto pnts = parents.at(ID);
			int minOrder = (int)graph.size();
			for (auto iter = pnts.begin(); iter != pnts.end(); iter++)
				if (idOrder.at(*iter) < minOrder)
					minOrder = idOrder.at(*iter);
			int firstPredecessor = RPO.at(minOrder);

			int newIDom = firstPredecessor;
			auto iter = pnts.begin();
			while (iter != pnts.end()) {
				if (IDom.at(*iter) != -1 && *iter != firstPredecessor) {
					//itersect(*iter, newIDom)
					int finger1 = *iter;
					int finger2 = newIDom;
					while (finger1 != finger2) {
						while (idOrder.at(finger1) > idOrder.at(finger2))
							finger1 = IDom.at(finger1);
						while (idOrder.at(finger2) > idOrder.at(finger1))
							finger2 = IDom.at(finger2);
					}
					newIDom = finger1;
				}
				iter++;
			}
			if (IDom.at(ID) != newIDom) {
				IDom[ID] = newIDom;
				changed = true;
			}
		}
	}
	//! after calculation, IDom[start] = 0, but it should be -1
	IDom[graph.begin()->first] = -1;
	return IDom;
}

//jmpiTgt和natTgt是生成Dom节点的上限，最多不超过函数体之外
map<int, vector<int>> genInvalidDoms(set<int>& invalids, const map<int, int>& IDom, const map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt) {
	map<int, vector<int>> res;
	for (auto& i : invalids) {
		int ID = IDom.at(i);
		res[i] = {};
		while (ID != -1) {
			res.at(i).push_back(ID);
			if (jmpiTgt.find(nodes.at(ID).getStart()) == jmpiTgt.end() && natTgt.find(nodes.at(ID).getStart()) == natTgt.end())
				break;
			ID = IDom.at(ID);
		}
	}
	return res;
}

map<int, vector<expr>> getCODECOPYOffsetAndSizeExpr(const map<int, EBasicBlock>& blocks, const map<int, int>& codecopyBlocks, z3::context& ctx) {
	map<int, vector<expr>> codecopyAddr2offsetAndSizeExpr;
	set<int> todoBlocks;
	for (auto& bb : codecopyBlocks)
		todoBlocks.insert(bb.second);
	for (auto& bb : todoBlocks) {
		vector<z3::expr> stack;
		for (int i = 0; i < 1024; i++)
			stack.push_back(ctx.bv_const(("s" + to_string(1024 - 1 - i)).c_str(), 256));
		map<string, z3::expr> memory;
		map<string, z3::expr> storage;
		z3::expr jumpiCond = ctx.bool_val(true);
		for (auto& i : blocks.at(bb).getInstrs()) {
			if (i.second == "CODECOPY")
				codecopyAddr2offsetAndSizeExpr[i.first] = { stack[stack.size() - 2], stack[stack.size() - 3] };
			symExecInstr(i.first, i.second, ctx, stack, memory, storage, jumpiCond);
		}
	}
	return codecopyAddr2offsetAndSizeExpr;
}

int getInvalidStart(const vector<int>& path, const map<int, ECFGNode>& nodes, const vector<int>& doms) {
	z3::context ctx;
	vector<expr> stack;
	map<string, expr> memory;
	map<string, expr> storage;
	expr jumpiCond = ctx.bool_val(true);

	map<int, InstrState*> domStates;//保存的应是未执行dom ID中的指令之前的状态
	InstrState* invState;
	for (size_t i = 0; i < path.size() - 1; i++) {//最后一个基本块为INVALID指令，因此不用执行
		auto& start = path[i];
		auto& next = path[i + 1];
		for (auto& instr : nodes.at(start).getInstrs()) {
			//here jumpiCond not used
			//displayRedMsg("Addr : " + to_string(instr.first) + " Instruction : " + instr.second);
			//displayStack(stack);
			symExecInstr(instr.first, instr.second, ctx, stack, memory, storage, jumpiCond);
		}
		if (count(doms.begin(), doms.end(), next) > 0) {
			//assert(domStates.find(next) == domStates.end());
			domStates[next] = new InstrState();
			domStates.at(next)->stack = stack;
			domStates.at(next)->memory = memory;
			domStates.at(next)->storage = storage;
		}
	}

	invState = new InstrState();
	invState->stack = stack;
	invState->memory = memory;
	invState->storage = storage;
	//displayStack(stack);
	//displayMemory(memory);
	//displayStorage(storage);

	int invalidStart = -1;
	//eg: 若pc为353时的指令为JUMPI，即将执行pc为354的INVALID指令，此时不能用353作为返回值
	int except = nodes.at(path[path.size() - 2]).getEnd();
	for (auto& d : doms) {
		bool match = false;
		for (auto& instr : nodes.at(d).getInstrs()) {
			if (instr.first == except)continue;

			InstrState* ptr = domStates.at(d);
			//displayRedMsg("Addr " + to_string(instr.first) + " : " + instr.second);
			//displayStack(stack);
			symExecInstr(instr.first, instr.second, ctx, ptr->stack, ptr->memory, ptr->storage, jumpiCond);

			bool equal = (ptr->stack.size() == invState->stack.size());
			if (equal)
				for (int i = 0; i < ptr->stack.size(); i++)
					if (ptr->stack[i].to_string() != invState->stack[i].to_string()) {
						equal = false; break;
					}
			//if (equal) {//需要对ptr以及invState进行双向检查(同时检查A包含于B以及B包含于A)
			//	for (auto& m : ptr->memory) {
			//		auto iter = invState->memory.find(m.first);
			//		if (iter == invState->memory.end()) { equal = false; break; }
			//		else if (m.second.to_string() != iter->second.to_string()) { equal = false; break; }
			//	}
			//	for (auto& m : invState->memory) {
			//		auto iter = ptr->memory.find(m.first);
			//		if (iter == ptr->memory.end()) { equal = false; break; }
			//		else if (m.second.to_string() != iter->second.to_string()) { equal = false; break; }
			//	}
			//}
			if (equal) {//同上对memory的检查
				for (auto& s : ptr->storage) {
					auto iter = invState->storage.find(s.first);
					if (iter == invState->storage.end()) { equal = false; break; }
					else if (s.second.to_string() != iter->second.to_string()) { equal = false; break; }
				}
				for (auto& s : invState->storage) {
					auto iter = ptr->storage.find(s.first);
					if (iter == ptr->storage.end()) { equal = false; break; }
					else if (s.second.to_string() != iter->second.to_string()) { equal = false; break; }
				}
			}
			if (equal) {
				//有可能出现在某一支配节点的执行过程中会先后出现状态匹配的情况，此时应尽量取靠后的那一种情况
				//有可能在assertion的执行过程中由于执行SHA3操作而改变内存的情况，因此不能比较memory的情况，目前为保险起见，保留对storage的检查
				//见 D:\SolidityExperiments\contracts\0x47d9d899bFb70CC53634e0Cd7eEa105217aD1649
				invalidStart = instr.first + Contract::getOpcodeSize(instr.second);
				match = true;
			}
		}
		if (match)break;
	}

	//delete domStates  and invState
	for (auto& s : domStates)
		delete s.second;
	delete invState;

	//delete potential returnDataSize
	if (returnDataSize != NULL)
		delete returnDataSize;
	returnDataSize = NULL;

	return invalidStart;
}

//used in recognizing the bytecode CFG's invalid related instructions
//invDirectIDs 存储的是invalid指令对应的函数调用深度尽可能少的invalid node
void getAllInvalidDirectIDs(const map<vector<int>, int>& jumpInfoMaps, const map<int, ECFGNode>& nodes, set<int>& invDirectIDs) {
	map<int, tuple<int, int>> invAddrIDJumpIn;
	for (auto& infomap : jumpInfoMaps) {
		auto& n = nodes.at(infomap.second);
		if (n.getBlockType() == BlockType::INVALID) {
			const string& jumpIn = n.getJumpIn();
			int addr = n.getStart();
			int funcIns = (int)count(jumpIn.begin(), jumpIn.end(), '_');
			if (invAddrIDJumpIn.find(addr) == invAddrIDJumpIn.end())
				invAddrIDJumpIn.insert(make_pair(addr, make_tuple(n.getID(), funcIns)));
			else
				if (get<1>(invAddrIDJumpIn.at(addr)) < funcIns)
					invAddrIDJumpIn[addr] = make_tuple(n.getID(), funcIns);
		}
	}

	for (auto& e : invAddrIDJumpIn)
		invDirectIDs.insert(get<0>(e.second));
}

void getInvalidDirectIDs(const set<int>& invAddrs, const map<int, ECFGNode>& nodes, set<int>& invDirectIDs) {
	//层序遍历寻找invAddrs的每个INVALID 地址对应的CFG中深度最浅的节点
	map<int, bool> invAddrVisited;
	for (auto& addr : invAddrs)
		invAddrVisited.insert(make_pair(addr, false));
	map<int, bool> nodesVisited;
	for (auto& n : nodes)
		nodesVisited.insert(make_pair(n.first, false));
	queue<int> nodeQue;
	nodeQue.push(0); nodesVisited.at(0) = true;
	while (!nodeQue.empty()) {
		int front = nodeQue.front();
		nodeQue.pop();
		const ECFGNode& node = nodes.at(front);
		if (invAddrVisited.find(node.getStart()) != invAddrVisited.end() && !invAddrVisited.at(node.getStart())) {
			invDirectIDs.insert(node.getID());
			invAddrVisited.at(node.getStart()) = true;
		}

		int fallsID = node.getFallsID();
		int jumpID = node.getJumpID();
		if (fallsID != -1 && !nodesVisited.at(fallsID)) {
			nodesVisited.at(fallsID) = true;
			nodeQue.push(fallsID);
		}

		if (jumpID != -1 && !nodesVisited.at(jumpID)) {
			nodesVisited.at(jumpID) = true;
			nodeQue.push(jumpID);
		}
	}
}

void getDstIDPaths(const map<int, set<int>>& edges, const set<int>& dstIDs, map<int, vector<int>>& paths) {
	set<int> visited;
	vector<int> dfs;
	dfs.push_back(0);

	while (!dfs.empty()) {
		int top = dfs.back();
		int flag = true;
		for (auto& i : edges.at(top))
			if (visited.find(i) == visited.end()) {
				dfs.push_back(i);
				visited.insert(i);
				flag = false;
				break;
			}

		if (flag)
			dfs.pop_back();
		else if (dstIDs.find(dfs.back()) != dstIDs.end() && (paths.find(dfs.back()) == paths.end() || paths.at(dfs.back()).size() > dfs.size()))
			paths[dfs.back()] = dfs;
	}
}
map<int, set<int>> getAddrRelatedNodes(const map<int, ECFGNode>& nodes) {
	map<int, set<int>> res;
	for (auto& n : nodes) {
		res[n.second.getStart()].insert(n.first);
	}
	return res;
}
//returns invAddr => related instruction start
map<int, int> getInvRelatedInstrsStart(const set<int>& invAddrs, const map<int, set<int>>& edges, map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt) {
	map<int, int> res;

	//genIDom生成所有节点的直接支配节点
	map<int, int> IDoms = genIDom(edges);

	//生成invAddrs集合中每个INVALID地址对应于CFG中深度最浅的invalid Node ID
	set<int> invDirectIDs; getInvalidDirectIDs(invAddrs, nodes, invDirectIDs);

	//生成invDirectIDs集合中每一个节点的支配节点集合
	map<int, vector<int>> invalidDoms = genInvalidDoms(invDirectIDs, IDoms, nodes, jmpiTgt, natTgt);

	//针对invDirectIDs集合中的每一个节点生成一条路径
	map<int, vector<int>> invPaths; getDstIDPaths(edges, invDirectIDs, invPaths);

	//针对每一个invalid指令生成对应的invalid检测指令的起始点
	for (auto& id : invalidDoms) {
		int instrStart = getInvalidStart(invPaths.at(id.first), nodes, id.second);
		if (instrStart == -1) {
			//这里的原因一般是因为对于SHA3的处理无法更精确导致的同一段指令执行两次时SHA3的输出不相同导致的

			//以下处理是通过取出距离INVALID节点最近的节点的指令序列
			//然后对该序列的最后几个指令进行模式匹配
			//模式1：DUPx, PUSHx tagX, JUMPI
			const map<int, string>& instrs = nodes.at(id.second[0]).getInstrs();
			if (instrs.size() > 3) {
				auto iter = instrs.rbegin();
				string last = iter->second; iter++;
				string last2 = iter->second; iter++;
				string last3 = iter->second;
				if (last == "JUMPI" && last2.find("PUSH") != string::npos && last3.find("DUP") != string::npos)
					res.insert(make_pair(nodes.at(id.first).getStart(), iter->first));
			}
		}
		else
			res.insert(make_pair(nodes.at(id.first).getStart(), instrStart));
	}

	return res;
}

bool reachable(const map<int, ECFGNode>& nodes, int start, int end) {
	list<int> queue;
	queue.push_back(start);
	set<int> visited;
	while (!queue.empty()) {
		int pnt = queue.front();
		visited.insert(pnt);
		queue.pop_front();
		if (pnt == end)
			return true;
		int fall = nodes.at(pnt).getFallsID();
		int jump = nodes.at(pnt).getJumpID();
		if (fall != -1 && visited.find(fall) == visited.end())
			queue.push_back(fall);
		if (jump != -1 && visited.find(jump) == visited.end())
			queue.push_back(jump);
	}

	return false;
}
bool reachable(const map<int, set<int>>& edges, int start, int end) {
	list<int> queue;
	queue.push_back(start);
	set<int> visited;
	while (!queue.empty()) {
		int pnt = queue.front();
		visited.insert(pnt);
		queue.pop_front();
		if (pnt == end)
			return true;
		for (auto& n : edges.at(pnt))
			if (visited.find(n) == visited.end())
				queue.push_back(n);
	}
	return false;
}

void getLoopCondBlock(const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, set<int>& loopCond, const set<int>& jmpiTgt, const set<int>& natTgt) {
	//all CFGs begin at block 0
	for (auto& n : nodes) {
		int jumpID = n.second.getJumpID();
		if (n.second.getBlockType() == BlockType::JUMP && edges.find(n.first) != edges.end()
			&& loopCond.find(jumpID) == loopCond.end()
			&& reachable(edges, jumpID, n.first)
			&& nodes.at(jumpID).getStart() < n.second.getStart()) {
			int addr = nodes.at(jumpID).getStart();
			if (jmpiTgt.find(addr) != jmpiTgt.end() || natTgt.find(addr) != natTgt.end())
				loopCond.insert(jumpID);
		}
	}
}

//reverseDFS类似与树的后序遍历，而不是对原图G的逆图G'进行遍历
void postDFS(int ID, const map<int, set<int>>& reEdges, set<int>& visited, vector<int>& stack) {
	if (visited.find(ID) == visited.end()) {
		visited.insert(ID);
		for (auto& e : reEdges.at(ID))
			postDFS(e, reEdges, visited, stack);
		stack.push_back(ID);
	}
}

void testSCC(const map<int, set<int>>& edges, map<int, set<int>>& scc, const set<int>& jmpiTgt, const set<int>& natTgt, const map<int, ECFGNode>& nodes) {
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

	for (auto& s : scc) {
		for (auto& n : s.second) {
			//cout << n << " ";
			if (s.second.size() < 2)
				break;

			for (auto& p : reEdges.at(n)) {
				if (s.second.find(p) == s.second.end()) {//存在其他强连通分量的入边
					int start = nodes.at(n).getStart();
					if (jmpiTgt.find(start) == jmpiTgt.end() && natTgt.find(start) == natTgt.end()) {
						cout << "强连通分量入口处可能为函数入口或函数跳出点";
						break;
					}
				}
			}
		}
		//cout << endl;
	}
}

//计算CFG的强连通分量，在节点个数大于2的连通分量中挑选一个代表节点加入loop
//然后计算这些代表节点能到达哪些节点（即为loop能够到达的节点）
/*Kosaraju算法
 *对原图G进行DFS，并将节点按照遍历完成时间从大到小排序
 *按照上述排序对逆图G'进行DFS，每次遍历得到的树的所有节点构成一个强连通分量
 */
void invalidLoopExists(const map<int, set<int>>& edges, set<int>& loopInvalids) {
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
		if (stack.size() > 1)//存在loop
			loop.insert(stack.back());
	}

	visited.clear();
	for (auto& i : loop) {
		vector<int> stack;
		stack.push_back(i);
		while (!stack.empty()) {
			int v = stack.back();
			bool flag = true;
			for (auto& e : edges.at(v))
				if (visited.find(e) == visited.end()) {
					if (edges.at(e).empty())
						loopInvalids.insert(e);
					visited.insert(e);
					stack.push_back(e);
					flag = false;
					break;
				}
			if (flag)
				stack.pop_back();
		}
	}
}

void invalidLoopExists(const map<int, set<int>>& edges, const set<int>& loopCondNodes, set<int>& invalids) {
	for (auto& cond : loopCondNodes) {
		list<int> queue;
		queue.push_back(cond);
		set<int> visited;
		while (!queue.empty()) {
			int pnt = queue.front();
			visited.insert(pnt);
			queue.pop_front();
			const set<int>& outs = edges.at(pnt);
			if (outs.size() == 0)
				invalids.insert(pnt);
			else for (auto& out : outs)
				if (visited.find(out) == visited.end())
					queue.push_back(out);
		}
	}
}

void symExecNode(int ID, map<int, string>& isRedundant, const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, z3::context& c, vector<z3::expr>& stack, map<string, z3::expr>& memory, map<string, z3::expr>& storage, z3::solver& solver) {
	if (isRedundant.find(ID) != isRedundant.end()) {
		isRedundant[ID] = "necessary";
		return;
	}

	bool go = false;
	for (auto& elem : isRedundant)
		if (elem.second != "necessary" && elem.second != "loop" && reachable(edges, ID, elem.first)) {
			go = true;
			break;
		}

	if (!go) return;

	expr jumpiCond = c.bool_val(true);
	const ECFGNode& node = nodes.at(ID);
	for (auto& instr : node.getInstrs()) {
		displayRedMsg("Addr : " + to_string(instr.first) + " Instruction : " + instr.second);
		displayStack(stack);
		symExecInstr(instr.first, instr.second, c, stack, memory, storage, jumpiCond);
	}

	const set<int>& es = edges.at(ID);
	if (es.size() == 1) {
		int targetID = *es.begin();
		if (node.getBlockType() != BlockType::JUMPI)
			symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, solver);
		else if (targetID == node.getFallsID()) {
			displayGreenMsg((!jumpiCond).simplify().to_string());

			//cout << "******************************" << endl;
			solver.push();
			solver.add((!jumpiCond).simplify());
			displayRedMsg(solver.to_smt2());
			z3::check_result chkRes = solver.check();
			if (chkRes == z3::sat || chkRes == z3::unknown)
				symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, solver);
			solver.pop();
		}
		else if (targetID == node.getJumpID()) {
			displayGreenMsg(jumpiCond.to_string());

			//cout << "******************************" << endl;
			solver.push();
			solver.add(jumpiCond);
			displayRedMsg(solver.to_smt2());
			z3::check_result chkRes = solver.check();
			if (chkRes == z3::sat || chkRes == z3::unknown)
				symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, solver);
			solver.pop();
		}
		else { assert(false); }
	}
	else {
		assert(es.size() == 2);
		displayGreenMsg(jumpiCond.to_string());
		//cout << "******************************" << endl;

		vector<expr>* stackPtr = NULL;
		map<string, expr>* memoryPtr = NULL;
		map<string, expr>* storagePtr = NULL;

		solver.push();
		solver.add(jumpiCond);
		displayRedMsg(solver.to_smt2());
		z3::check_result jumpRes = solver.check();
		if (jumpRes == z3::sat || jumpRes == z3::unknown) {
			stackPtr = new vector<expr>(stack);
			memoryPtr = new map<string, expr>(memory);
			storagePtr = new map<string, expr>(storage);
			symExecNode(node.getJumpID(), isRedundant, edges, nodes, c, stack, memory, storage, solver);
		}
		solver.pop();

		displayGreenMsg((!jumpiCond).simplify().to_string());
		//cout << "******************************" << endl;
		solver.push();
		solver.add((!jumpiCond).simplify());
		displayRedMsg(solver.to_smt2());

		z3::check_result natRes = solver.check();
		if (natRes == z3::sat || jumpRes == z3::unknown)
			if (stackPtr == NULL || memoryPtr == NULL || storagePtr == NULL)
				symExecNode(node.getFallsID(), isRedundant, edges, nodes, c, stack, memory, storage, solver);
			else
				symExecNode(node.getFallsID(), isRedundant, edges, nodes, c, *stackPtr, *memoryPtr, *storagePtr, solver);
		solver.pop();
		delete stackPtr;
		delete memoryPtr;
		delete storagePtr;
	}
}

void generateInvalidDotGraph(const map<int, ECFGNode>& nodes, string fileName, const map<int, set<int>>& edges) {
	ofstream outFile(fileName);
	string dotFile = "digraph G { \r\n";
	dotFile += "size = \"4,4\";\r\n";
	for (auto& n : nodes) {
		string blockName = "Node_" + to_string(n.first);
		string label = "Node_" + to_string(n.first) + "#" + to_string(n.second.getStart()) + "-" + to_string(n.second.getEnd());
		label += "$" + n.second.getJumpIn();
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

		//能通往INVALID指令
		if (edges.find(n.first) != edges.end())
			color += ", shape = Mrecord";

		string nodeLabel = "[label = \"" + label + "\"" + color + "]";
		//string nodeLabel = "";
		dotFile += blockName + nodeLabel + "\r\n";
		for (auto p : n.second.getParents()) {
			if (p == -1)
				continue;
			string parentName = "Node_" + to_string(p);

			//invalid related edge
			string edgeAttr = "";
			if (edges.find(p) != edges.end() && edges.at(p).find(n.first) != edges.at(p).end())
				edgeAttr += "[color = blue]";

			dotFile += "\t" + parentName + " -> " + blockName + edgeAttr + ";\r\n";
		}
	}
	dotFile += "}";
	if (!outFile) {
		cout << "Fail to open File : " << fileName << endl;
	}
	outFile << dotFile;
	outFile.close();
}

static map<int, map<vector<int>, expr>> invPathConstraints;
void symExecNode(int ID, const
	map<int, string>& isRedundant, const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, z3::context& c, vector<expr>& stack, map<string, expr>& memory, map<string, expr>& storage, vector<int>& visited, expr& cond) {
	visited.push_back(ID);
	if (isRedundant.find(ID) != isRedundant.end()) {
		if (invPathConstraints.find(ID) == invPathConstraints.end())
			invPathConstraints[ID] = {};
		invPathConstraints.at(ID).insert(make_pair(visited, cond));
		return;
	}
	bool go = false;
	for (auto& elem : isRedundant)
		if (elem.second != "loop" && reachable(edges, ID, elem.first)) {
			go = true;
			break;
		}

	if (!go) return;

	expr jumpiCond = c.bool_val(true);
	const ECFGNode& node = nodes.at(ID);
	for (auto& instr : node.getInstrs()) {
		//displayRedMsg("addr : " + to_string(instr.first) + " instruction : " + instr.second);
		//displayStack(stack);
		symExecInstr(instr.first, instr.second, c, stack, memory, storage, jumpiCond);
	}

	const set<int>& es = edges.at(ID);
	if (es.size() == 1) {
		int targetID = *es.begin();
		if (node.getBlockType() != BlockType::JUMPI)
			symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, visited, cond);
		else if (targetID == node.getFallsID()) {
			//displayGreenMsg((!jumpiCond).simplify().to_string());
			//cout << "******************************" << endl;
			cond = (cond && !jumpiCond).simplify();
			symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, visited, cond);
		}
		else if (targetID == node.getJumpID()) {
			//displayGreenMsg(jumpiCond.to_string());
			//cout << "******************************" << endl;
			cond = (cond && jumpiCond).simplify();
			symExecNode(targetID, isRedundant, edges, nodes, c, stack, memory, storage, visited, cond);
		}
		else { assert(false); }
	}
	else {
		assert(es.size() == 2);
		//displayGreenMsg(jumpiCond.to_string());
		//cout << "******************************" << endl;

		vector<int> visited1, visited2; visited1 = visited2 = visited;
		vector<expr> stack1, stack2; stack1 = stack2 = stack;
		map<string, expr> memory1, memory2; memory1 = memory2 = memory;
		map<string, expr> storage1, storage2; storage1 = storage2 = storage;

		expr cond1 = (cond && jumpiCond).simplify();
		symExecNode(node.getJumpID(), isRedundant, edges, nodes, c, stack1, memory1, storage1, visited1, cond1);

		expr cond2 = (cond && !jumpiCond).simplify();
		symExecNode(node.getFallsID(), isRedundant, edges, nodes, c, stack2, memory2, storage2, visited2, cond2);
	}
}

void isRedundant(const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt, vector<int>& redundantInvs, const string& name) {
	//map<int, set<int>> edges;
	//pruningInvalids(nodes, edges);

	generateInvalidDotGraph(nodes, name + ".dot", edges);

	set<int> loopCondNodes;
	getLoopCondBlock(edges, nodes, loopCondNodes, jmpiTgt, natTgt);


	set<int> loopInvalids;
	//得到所有可能经过循环的INVALID基本块
	invalidLoopExists(edges, loopCondNodes, loopInvalids);

	map<int, string> isRedundant;
	for (auto& n : nodes)
		if (n.second.getBlockType() == BlockType::INVALID)
			if (loopInvalids.find(n.first) == loopInvalids.end())
				isRedundant[n.first] = "unknown";
			else
				isRedundant[n.first] = "loop";

	z3::context c;
	vector<expr> stack;
	map<string, expr> memory;
	map<string, expr> storage;

	Z3_global_param_set("timeout", "5000");
	z3::params p(c);
	p.set("mul2concat", true);
	z3::tactic t =
		with(z3::tactic(c, "simplify"), p) &
		z3::tactic(c, "solve-eqs") &
		z3::tactic(c, "bit-blast") &
		z3::tactic(c, "aig") &
		z3::tactic(c, "sat");
	z3::solver solver = t.mk_solver();

	symExecNode(0, isRedundant, edges, nodes, c, stack, memory, storage, solver);

	for (auto& elem : isRedundant)
		if (elem.second == "unknown")
			redundantInvs.push_back(elem.first);
}
static mutex contextMtx;
static mutex checkMtx;
void solverTask(const expr& cond, z3::check_result& res) {
	if (res != z3::sat) {//后续需要实验看能否改成 res != z3::sat || res != z3::unknown
		contextMtx.lock();
		z3::context& ctx = cond.ctx();
		z3::context c;
		z3::params p(c);
		p.set("mul2concat", true);
		z3::tactic t =
			with(z3::tactic(c, "simplify"), p) &
			z3::tactic(c, "solve-eqs") &
			z3::tactic(c, "bit-blast") &
			z3::tactic(c, "aig") &
			z3::tactic(c, "sat");
		z3::solver s = t.mk_solver();
		expr e = to_expr(c, Z3_translate(ctx, cond, c));
		s.add(e);
		//cout << cond.simplify().to_string() << endl;
		//cout << "**********************************" << endl;
		contextMtx.unlock();
		z3::check_result chkRes = s.check();
		checkMtx.lock();
		if (res == z3::unsat) {
			res = chkRes;
		}
		else if (res == z3::unknown && chkRes == z3::sat) {
			res = z3::sat;
		}
		checkMtx.unlock();
	}
}

void parallelSolve(const map<int, set<int>>& edges, const map<int, ECFGNode>& nodes, const set<int>& jmpiTgt, const set<int>& natTgt, set<int>& loopInvalids, vector<int>& redundantInvs) {

	////在一些情况下并不适用，因为并非所有的loopCond基本块均是jmpiTgt或者natTgt中的一种
	//set<int> loopCondNodes;
	//getLoopCondBlock(edges, nodes, loopCondNodes, jmpiTgt, natTgt);
	//set<int> loopInvalids;
	////得到所有可能经过循环的INVALID基本块
	//invalidLoopExists(edges, loopCondNodes, loopInvalids);

	//set<int> loopInvalids;
	invalidLoopExists(edges, loopInvalids);

	map<int, string> isRedundant;
	for (auto& n : nodes)
		if (n.second.getBlockType() == BlockType::INVALID)
			if (loopInvalids.find(n.first) == loopInvalids.end())
				isRedundant[n.first] = "unknown";
			else
				isRedundant[n.first] = "loop";

	z3::context c;
	Z3_global_param_set("timeout", "10000");
	vector<expr> stack;
	map<string, expr> memory;
	map<string, expr> storage;

	invPathConstraints.clear();
	vector<int> visited;
	expr cond = c.bool_val(true);

	symExecNode(0, isRedundant, edges, nodes, c, stack, memory, storage, visited, cond);
	//需要在context还未被释放之前delete，因为后续函数可能还会用到returnDataSize，到时候再delete会出现错误
	if (returnDataSize != NULL)
		delete returnDataSize;
	returnDataSize = NULL;

	const unsigned int threadNum = thread::hardware_concurrency();
	for (auto& inv : invPathConstraints) {
		z3::check_result res = z3::unsat;
		thread* thds = new thread[threadNum];
		unsigned int solveNum = 0;
		for (auto& con : inv.second) {
			thds[solveNum] = thread(solverTask, ref(con.second), ref(res));
			solveNum++;
			if (solveNum >= threadNum) {
				solveNum = 0;
				for (unsigned int i = 0; i < threadNum; i++)
					thds[i].join();

				delete[] thds;
				if (res == z3::unknown || res == z3::sat)
					break;
				thds = new thread[threadNum];
			}
		}
		if (res == z3::unsat) {
			for (unsigned int i = 0; i < solveNum; i++)
				thds[i].join();
			delete[] thds;
		}
		//displayRedMsg("End the analysis of Node ID " + to_string(inv.first));
		if (res == z3::unsat)
			redundantInvs.push_back(inv.first);
	}
	invPathConstraints.clear();//必须保证expr的正确析构
}