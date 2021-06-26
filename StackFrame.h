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
	//��������ָʾz3Expr�Ƿ������ڷ��Ż���ջ��Ԫ��
	//���ڴ�����Ҫʹ�÷��Ż���ջ�����з���ִ�е��������ʹ��[s0, s1, s2, ... , s1023]�����л�����ķ���ִ��
	//�����ڽ���SHA3������memory/storege��load/store����ʱ��Ҫ�鿴��Щָ��������ı��ʽ���Ƿ�����Щ����ֵ
	//������з���ֵ�Ļ���Ҫ��������������
	//�����ڲ�ͬ��ַ����SHA3ָ���ʱջ����������������memory�ж�Ӧ�ı��ʽ��Ϊs5,s6������������ַ��SHA3ָ��Ľ��Ӧ�÷ֱ�ΪSHA3#s5_s6_1��SHA3#s5_s6_2
	//bool symbolic;

	//��¼ĳһ���ʽ�����
	//ÿ�ζ�һ���µĻ��������symExecInstr����ʱ����ÿ�����ű��ʽ����ȼ�1
	//static map<string, int> exprDepth;

	//�洢memory��storage��ص�symbolic Expr
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