#pragma once

#include<string>
#include <map>
#include <tuple>
#include <set>
using namespace std;
enum class CostType { zero, base, verylow, low, mid, high, extcode };
class Opcode {//more thing to add
	static map<int, tuple<int, int>> operations;
	static map<int, string> mnemonics;//0x00 => STOP
	static map<string, int> opcodes;//STOP => 0x00
	static map<string, CostType> costTypes;
	static map<CostType, int> costs;
	static set<string> memOpcodes;
	static void initOperations() {
		operations[0x00] = make_tuple(0, 0);
		operations[0x01] = make_tuple(2, 1);
		operations[0x02] = make_tuple(2, 1);
		operations[0x03] = make_tuple(2, 1);
		operations[0x04] = make_tuple(2, 1);
		operations[0x05] = make_tuple(2, 1);
		operations[0x06] = make_tuple(2, 1);
		operations[0x07] = make_tuple(2, 1);
		operations[0x08] = make_tuple(3, 1);
		operations[0x09] = make_tuple(3, 1);
		operations[0x0a] = make_tuple(2, 1);
		operations[0x0b] = make_tuple(2, 1);

		operations[0x10] = make_tuple(2, 1);
		operations[0x11] = make_tuple(2, 1);
		operations[0x12] = make_tuple(2, 1);
		operations[0x13] = make_tuple(2, 1);
		operations[0x14] = make_tuple(2, 1);
		operations[0x15] = make_tuple(1, 1);
		operations[0x16] = make_tuple(2, 1);
		operations[0x17] = make_tuple(2, 1);
		operations[0x18] = make_tuple(2, 1);
		operations[0x19] = make_tuple(1, 1);
		operations[0x1a] = make_tuple(2, 1);
		operations[0x1b] = make_tuple(2, 1);//SHL
		operations[0x1c] = make_tuple(2, 1);//SHR
		operations[0x1d] = make_tuple(2, 1);//SAR

		operations[0x20] = make_tuple(2, 1);

		operations[0x30] = make_tuple(0, 1);
		operations[0x31] = make_tuple(1, 1);
		operations[0x32] = make_tuple(0, 1);
		operations[0x33] = make_tuple(0, 1);
		operations[0x34] = make_tuple(0, 1);
		operations[0x35] = make_tuple(1, 1);
		operations[0x36] = make_tuple(0, 1);
		operations[0x37] = make_tuple(3, 0);
		operations[0x38] = make_tuple(0, 1);
		operations[0x39] = make_tuple(3, 0);
		operations[0x3a] = make_tuple(0, 1);
		operations[0x3b] = make_tuple(1, 1);
		operations[0x3c] = make_tuple(4, 0);
		operations[0x3d] = make_tuple(0, 1);
		operations[0x3e] = make_tuple(3, 0);
		operations[0x3f] = make_tuple(1, 1);

		operations[0x40] = make_tuple(1, 1);
		operations[0x41] = make_tuple(0, 1);
		operations[0x42] = make_tuple(0, 1);
		operations[0x43] = make_tuple(0, 1);
		operations[0x44] = make_tuple(0, 1);
		operations[0x45] = make_tuple(0, 1);
		//Istanbul added opcodes
		operations[0x46] = make_tuple(0, 1);//CHAINID
		operations[0x47] = make_tuple(0, 1);//SELFBALANCE

		operations[0x50] = make_tuple(1, 0);
		operations[0x51] = make_tuple(1, 1);
		operations[0x52] = make_tuple(2, 0);
		operations[0x53] = make_tuple(2, 0);
		operations[0x54] = make_tuple(1, 1);
		operations[0x55] = make_tuple(2, 0);
		operations[0x56] = make_tuple(1, 0);
		operations[0x57] = make_tuple(2, 0);
		operations[0x58] = make_tuple(0, 1);
		operations[0x59] = make_tuple(0, 1);
		operations[0x5a] = make_tuple(0, 1);
		operations[0x5b] = make_tuple(0, 0);

		for (int i = 0x60; i <= 0x7f; i++)
			operations[i] = make_tuple(0, 1);
		for (int i = 0x80; i <= 0x8f; i++)
			operations[i] = make_tuple(i - 0x80 + 1, i - 0x80 + 2);
		for (int i = 0x90; i <= 0x9f; i++)
			operations[i] = make_tuple(i - 0x90 + 2, i - 0x90 + 2);

		for (int i = 0xa0; i <= 0xa4; i++)
			operations[i] = make_tuple(i - 0xa0 + 2, 0);

		operations[0xf0] = make_tuple(3, 1);
		operations[0xf1] = make_tuple(7, 1);
		operations[0xf2] = make_tuple(7, 1);
		operations[0xf3] = make_tuple(2, 0);
		operations[0xf4] = make_tuple(6, 1);
		operations[0xf5] = make_tuple(4, 1);
		operations[0xfa] = make_tuple(6, 1);
		operations[0xfd] = make_tuple(2, 0);
		operations[0xfe] = make_tuple(0, 0);
		operations[0xff] = make_tuple(1, 0);
	}
	static void initMnemonics() {
		mnemonics[0x00] = "STOP";
		mnemonics[0x01] = "ADD";
		mnemonics[0x02] = "MUL";
		mnemonics[0x03] = "SUB";
		mnemonics[0x04] = "DIV";
		mnemonics[0x05] = "SDIV";
		mnemonics[0x06] = "MOD";
		mnemonics[0x07] = "SMOD";
		mnemonics[0x08] = "ADDMOD";
		mnemonics[0x09] = "MULMOD";
		mnemonics[0x0a] = "EXP";
		mnemonics[0x0b] = "SIGNEXTEND";

		mnemonics[0x10] = "LT";
		mnemonics[0x11] = "GT";
		mnemonics[0x12] = "SLT";
		mnemonics[0x13] = "SGT";
		mnemonics[0x14] = "EQ";
		mnemonics[0x15] = "ISZERO";
		mnemonics[0x16] = "AND";
		mnemonics[0x17] = "OR";
		mnemonics[0x18] = "XOR";
		mnemonics[0x19] = "NOT";
		mnemonics[0x1a] = "BYTE";
		mnemonics[0x1b] = "SHL";//shift left shl(x, y) logical shift left y by x bits
		mnemonics[0x1c] = "SHR";//shift right shr(x ,y) logical shift right y by x bits
		mnemonics[0x1d] = "SAR";//arithmetic shift right sar(x, y) arithmetic shift right y by x bits

		mnemonics[0x20] = "SHA3";

		mnemonics[0x30] = "ADDRESS";
		mnemonics[0x31] = "BALANCE";
		mnemonics[0x32] = "ORIGIN";
		mnemonics[0x33] = "CALLER";
		mnemonics[0x34] = "CALLVALUE";
		mnemonics[0x35] = "CALLDATALOAD";
		mnemonics[0x36] = "CALLDATASIZE";
		mnemonics[0x37] = "CALLDATACOPY";
		mnemonics[0x38] = "CODESIZE";
		mnemonics[0x39] = "CODECOPY";
		mnemonics[0x3a] = "GASPRICE";
		mnemonics[0x3b] = "EXTCODESIZE";
		mnemonics[0x3c] = "EXTCODECOPY";
		mnemonics[0x3d] = "RETURNDATASIZE";
		mnemonics[0x3e] = "RETURNDATACOPY";
		mnemonics[0x3f] = "EXTCODEHASH";

		mnemonics[0x40] = "BLOCKHASH";
		mnemonics[0x41] = "BASE";
		mnemonics[0x42] = "TIMESTAMP";
		mnemonics[0x43] = "NUMBER";
		mnemonics[0x44] = "DIFFICULTY";
		mnemonics[0x45] = "GASLIMIT";
		mnemonics[0x46] = "CHAINID";
		mnemonics[0x47] = "SELFBALANCE";

		mnemonics[0x50] = "POP";
		mnemonics[0x51] = "MLOAD";
		mnemonics[0x52] = "MSTORE";
		mnemonics[0x53] = "MSTORE8";
		mnemonics[0x54] = "SLOAD";
		mnemonics[0x55] = "SSTORE";
		mnemonics[0x56] = "JUMP";
		mnemonics[0x57] = "JUMPI";
		mnemonics[0x58] = "PC";
		mnemonics[0x59] = "MSIZE";
		mnemonics[0x5a] = "GAS";
		mnemonics[0x5b] = "JUMPDEST";

		for (int i = 0x60; i <= 0x7f; i++)
			mnemonics[i] = "PUSH" + to_string(i - 0x60 + 1);

		for (int i = 0x80; i <= 0x8f; i++)
			mnemonics[i] = "DUP" + to_string(i - 0x80 + 1);

		for (int i = 0x90; i <= 0x9f; i++)
			mnemonics[i] = "SWAP" + to_string(i - 0x90 + 1);

		for (int i = 0xa0; i <= 0xa4; i++)
			mnemonics[i] = "LOG" + to_string(i - 0xa0);

		mnemonics[0xf0] = "CREATE";
		mnemonics[0xf1] = "CALL";
		mnemonics[0xf2] = "CALLCODE";
		mnemonics[0xf3] = "RETURN";
		mnemonics[0xf4] = "DELEGATECALL";
		mnemonics[0xf5] = "CREATE2";
		mnemonics[0xfa] = "STATICCALL";
		mnemonics[0xfd] = "REVERT";
		mnemonics[0xfe] = "INVALID";
		mnemonics[0xff] = "SELFDESTRUCT";
	}
	static void initOpcodes() {
		for (auto mne : mnemonics)
			opcodes[mne.second] = mne.first;
	}
	static void initCostTypes() {
		costTypes["STOP"] = CostType::zero;
		costTypes["RETURN"] = CostType::zero;
		costTypes["REVERT"] = CostType::zero;

		costTypes["ADDRESS"] = CostType::base;
		costTypes["ORIGIN"] = CostType::base;
		costTypes["CALLER"] = CostType::base;
		costTypes["CALLVALUE"] = CostType::base;
		costTypes["CALLDATASIZE"] = CostType::base;
		costTypes["CODESIZE"] = CostType::base;
		costTypes["GASPRICE"] = CostType::base;
		costTypes["BASE"] = CostType::base;
		costTypes["TIMESTAMP"] = CostType::base;
		costTypes["NUMBER"] = CostType::base;
		costTypes["DIFFICULTY"] = CostType::base;
		costTypes["GASLIMIT"] = CostType::base;
		costTypes["RETURNDATASIZE"] = CostType::base;
		costTypes["POP"] = CostType::base;
		costTypes["PC"] = CostType::base;
		costTypes["MSIZE"] = CostType::base;
		costTypes["GAS"] = CostType::base;

		costTypes["ADD"] = CostType::verylow;
		costTypes["SUB"] = CostType::verylow;
		costTypes["NOT"] = CostType::verylow;
		costTypes["LT"] = CostType::verylow;
		costTypes["GT"] = CostType::verylow;
		costTypes["SLT"] = CostType::verylow;
		costTypes["SGT"] = CostType::verylow;
		costTypes["EQ"] = CostType::verylow;
		costTypes["ISZERO"] = CostType::verylow;
		costTypes["AND"] = CostType::verylow;
		costTypes["OR"] = CostType::verylow;
		costTypes["XOR"] = CostType::verylow;
		costTypes["BYTE"] = CostType::verylow;
		costTypes["CALLDATALOAD"] = CostType::verylow;
		costTypes["MLOAD"] = CostType::verylow;
		costTypes["MSTORE"] = CostType::verylow;
		costTypes["MSTORE8"] = CostType::verylow;
		for (int i = 0x60; i <= 0x7f; i++)
			costTypes["PUSH" + to_string(i - 0x60 + 1)] = CostType::verylow;

		for (int i = 0x80; i <= 0x8f; i++)
			costTypes["DUP" + to_string(i - 0x80 + 1)] = CostType::verylow;

		for (int i = 0x90; i <= 0x9f; i++)
			costTypes["SWAP" + to_string(i - 0x90 + 1)] = CostType::verylow;

		costTypes["MUL"] = CostType::low;
		costTypes["DIV"] = CostType::low;
		costTypes["SDIV"] = CostType::low;
		costTypes["MOD"] = CostType::low;
		costTypes["SMOD"] = CostType::low;
		costTypes["SIGNEXTEND"] = CostType::low;

		costTypes["ADDMOD"] = CostType::mid;
		costTypes["MULMOD"] = CostType::mid;
		costTypes["JUMP"] = CostType::mid;

		costTypes["JUMPI"] = CostType::high;

		costTypes["EXTCODESIZE"] = CostType::extcode;

		costs[CostType::zero] = 0;
		costs[CostType::base] = 2;
		costs[CostType::verylow] = 3;
		costs[CostType::low] = 5;
		costs[CostType::mid] = 8;
		costs[CostType::high] = 10;
		costs[CostType::extcode] = 700;
	}
public:
	static void init() {
		initOperations();
		initMnemonics();
		initOpcodes();
		initCostTypes();

		memOpcodes.insert("SHA3");

		memOpcodes.insert("CALLDATACOPY");
		memOpcodes.insert("CODECOPY");
		memOpcodes.insert("EXTCODECOPY");
		memOpcodes.insert("RETURNDATACOPY");

		memOpcodes.insert("MLOAD");
		memOpcodes.insert("MSTORE");
		memOpcodes.insert("MSTORE8");

		memOpcodes.insert("CREATE");
		memOpcodes.insert("CALL");
		memOpcodes.insert("CALLCODE");
		memOpcodes.insert("RETURN");
		memOpcodes.insert("DELEGATECALL");
		memOpcodes.insert("STATICCALL");
		memOpcodes.insert("REVERT");
	}

	static const string& getMnemonics(int bytecode) {
		return mnemonics.at(bytecode);
	}
	static bool exists(int bytecode) {
		return mnemonics.find(bytecode) != mnemonics.end();
	}
	static int getOpcode(const string& mne) {
		return opcodes.at(mne);
	}
	static const tuple<int, int>& getOperation(int bytecode) {
		return operations.at(bytecode);
	}

	static bool isMemOpcode(string mne) {
		return memOpcodes.find(mne) != memOpcodes.end();
	}

	static int opBaseCost(string mne) {
		return costs.at(costTypes.at(mne));
	}
};