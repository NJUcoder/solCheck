#pragma once
#include <boost/any.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include <string>
#include <iostream>
#ifdef _WIN32
#include <c++/z3++.h>
#endif
#ifdef __linux__
#include "z3++.h"
#endif
using namespace std;
using boost::multiprecision::int256_t;
using boost::multiprecision::uint256_t;
extern z3::context ctx;
enum class StackType {
	NODEF,
	EXPR,
	CONSTANT
};
class StackFrame {
	StackType type;//EXPR CONSTANT

	string name;//stack_position
	boost::multiprecision::int256_t value;

public:
	static z3::context c;
	z3::expr z3Expr;
	//这里用来指示z3Expr是否依赖于符号化的栈中元素
	//由于存在需要使用符号化的栈来进行符号执行的情况，即使用[s0, s1, s2, ... , s1023]来进行基本块的符号执行
	//所以在进行SHA3操作、memory/storege的load/store操作时需要查看这些指令操作数的表达式中是否含有这些符号值
	//如果含有符号值的话需要进行重命名操作
	//比如在不同地址处的SHA3指令，此时栈顶的两个操作数在memory中对应的表达式均为s5,s6，那这两个地址的SHA3指令的结果应该分别为SHA3#s5_s6_1和SHA3#s5_s6_2
	//bool symbolic;

	//记录某一表达式的深度
	//每次对一个新的基本块进行symExecInstr操作时，将每个符号表达式的深度加1
	//static map<string, int> exprDepth;

	//存储memory和storage相关的symbolic Expr
	//static set<string> symbolicExpr;

public:
	StackFrame() : type(StackType::NODEF), z3Expr(c)/*, symbolic(false)*/ {}
	StackFrame(string name) : type(StackType::EXPR), name(name), z3Expr(c)/*, symbolic(false)*/ {}
	StackFrame(boost::multiprecision::int256_t value) : type(StackType::CONSTANT), value(value), z3Expr(c)/*, symbolic(false)*/ {}
	StackType getType() const { return type; }
	void setType(StackType type) { this->type = type; }
	string getName() const {
		assert(type == StackType::EXPR);
		return name;
	}
	void setName(string name) {
		assert(type == StackType::EXPR);
		this->name = name;
	}

	boost::multiprecision::int256_t getValue() const {
		assert(type == StackType::CONSTANT);
		return value;
	}
	boost::multiprecision::uint256_t getUnsignedValue() const {
		assert(type == StackType::CONSTANT);
		return uint256_t(value);
	}
	void setValue(boost::multiprecision::int256_t value) {
		assert(type == StackType::CONSTANT);
		this->value = value;
	}
	void setValue(boost::multiprecision::uint256_t value) {
		assert(type == StackType::CONSTANT);
		this->value = int256_t(value);
	}
	void setValue(int value) {
		assert(type == StackType::CONSTANT);
		this->value = value;
	}

	string getExpr() const {
		switch (type) {
		case StackType::EXPR:return name;
		case StackType::CONSTANT:return boost::lexical_cast<std::string>(value);
		default:
			cout << "Wrong type" << endl;
			return "wrongExpr";
		}
	}
	static z3::expr genZ3Expr(int256_t value) {
		z3::expr res = c.bv_val(boost::lexical_cast<string>(value).c_str(), 256);
		return res;
	}
	static z3::expr genZ3Expr(uint256_t value) {
		z3::expr res = c.bv_val(boost::lexical_cast<string>(value).c_str(), 256);
		return res;
	}
	static z3::expr genZ3Expr(string name) {
		z3::expr res = c.bv_const(name.c_str(), 256);
		return res;
	}
	//static bool exprContains(string expr) {
	//	return exprDepth.find(expr) != exprDepth.end();
	//}
};