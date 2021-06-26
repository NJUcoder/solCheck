#pragma once
#include <string>
#include <vector>
#include <iostream>
#include <assert.h>
extern bool isNumerical(std::string s);
//bool Contract::isNumerical(string s);
using namespace std;
class Operand {
	//x type not used currently
	string type;//int array
	unsigned int bits;

	//123(constant number)/mu_S_0(stack_position)
	//temp(temporary variable)
	//		temp8 : 8 bits(1 byte) variable
	//		temp256 : 256 bits(32 bytes) variable
	//		tempN : N bits(N / 8 bytes) variable
	string value;
	static int num8;
	static int num256;
	static int num512;

	//used in SSA generation
	//未转化成SSA之前，index均为-1，此时index无作用
	//转化为SSA之后 ，index开始赋值
	int index;
public:
	Operand(string type, unsigned int bits, string value) :type(type), bits(bits), value(value), index(-1) {}
	Operand(string type, unsigned int bits, string value, int index) :type(type), bits(bits), value(value), index(index) {}
	string getStr() const {
		if (isNumerical(value))
			return value;
		else
			return value + "#" + to_string(index);
	}
	unsigned int getBits() const {
		return bits;
	}
	static void resetNum() {
		num8 = num256 = num512 = 0;
	}
	static int getNum8() {
		int temp = num8;
		num8++;
		return temp;
	}
	static int getNum256() {
		int temp = num256;
		num256++;
		return temp;
	}
	static int getNum512() {
		int temp = num512;
		num512++;
		return temp;
	}
	string getValue()const {
		return value;
	}
	void setValue(string value) { this->value = value; }

	int getIndex()const {
		return index;
	}
	void setIndex(int index) {
		this->index = index;
	}
};
enum class LeftOp {
	RAN, ASSIGNMENT, LESS, GREATER, EQUAL, NOT_EQUAL
};
class Expr {
	//Case 1 : left = right[0] op right[1]
	//Case 2 : left = right[0]
	//Case 3 : left lop right[0]
	//Case 4 : left lop right[0] op right[1]
	Operand left;

	vector<Operand> right;//the operand order is imporant!!!
	//add sub mul div, etc.
	//indexOf : []
	//zext, sext, truncate
	string op;//! right operator(1-ary : not, 2-ary : and,or, etc.)

	bool isMultiAry;//Case 1 and 4:true / Case 2 and 3:false
	LeftOp lop;
public:
	bool isRedundant() {//这里的redundant指的是生成的约束对于求解过程是冗余的
		if (right.size() == 1 && isNumerical(right[0].getValue()))
			return true;
		else
			return false;
	}
	//!? left = right
	Expr(Operand left, Operand right) :left(left), op("null"), isMultiAry(false), lop(LeftOp::ASSIGNMENT) {
		this->right.push_back(right);
	}
	//!? left = r1 op r2
	Expr(Operand left, Operand r1, string op, Operand r2) : left(left), op(op), isMultiAry(true), lop(LeftOp::ASSIGNMENT) {//! be careful about the order r1 op r2
		this->right.push_back(r1);
		this->right.push_back(r2);
	}
	Expr(const Expr& e) : left(e.left), right(e.right), op(e.op), isMultiAry(e.isMultiAry), lop(e.lop) {
	}
	//!? int(bits) : left lop r1
	Expr(unsigned int bits, string left, LeftOp lop, string right) : left("int", bits, left), op("null"), isMultiAry(false), lop(lop) {
		this->right.push_back(Operand("int", bits, right));
	}
	//!? int(bits) : left = r1
	Expr(unsigned int bits, string left, string r1) : left("int", bits, left), op("null"), isMultiAry(false), lop(LeftOp::ASSIGNMENT) {
		this->right.push_back(Operand("int", bits, r1));
	}
	//!? int(bits) : varName_leftIdx = varName_rightIdx
	Expr(unsigned int bits, string varName, int leftIdx, int rightIdx) : left("int", bits, varName, leftIdx), op("null"), isMultiAry(false), lop(LeftOp::ASSIGNMENT) {
		this->right.push_back(Operand("int", bits, varName, rightIdx));
	}
	//!? int(bits) : left = op r1
	Expr(unsigned int bits, string left, string op, string r1) : left("int", bits, left), op(op), isMultiAry(false), lop(LeftOp::ASSIGNMENT) {
		this->right.push_back(Operand("int", bits, r1));
	}
	//!? int(bits) : left = r1 op r2
	Expr(unsigned int bits, string left, string r1, string op, string r2) : left("int", bits, left), op(op), isMultiAry(true), lop(LeftOp::ASSIGNMENT) {
		this->right.push_back(Operand("int", bits, r1));
		this->right.push_back(Operand("int", bits, r2));
	}
	string getLopStr() const {
		switch (lop) {
		case LeftOp::ASSIGNMENT:return "=";
		case LeftOp::LESS:return "<";
		case LeftOp::GREATER:return ">";
		case LeftOp::EQUAL:return "==";
		case LeftOp::NOT_EQUAL:return "!=";
		default: return "nodef";
		}
	}
	void print() const {
		cout << getExprString() << endl;
	}
	string getExprString() const {
		string exprStr = left.getStr() + " " + getLopStr() + " ";
		if (op != "null")
			exprStr += op + "(";
		exprStr += right[0].getStr();
		for (size_t i = 1; i < right.size(); i++) //multi-ary
			exprStr += ", " + right[i].getStr();
		if (op != "null")
			exprStr += ")";
		return exprStr;
	}
	string getLeftName() const {
		return left.getValue();
	}
	string getRightName(int i) const {
		assert(right.size() > size_t(i));
		return right[i].getValue();
	}
	size_t getRightNum() const {
		return right.size();
	}
	void setLeftIndex(int idx) {
		left.setIndex(idx);
	}
	void setRightIndex(int idx, int oIdx) {//oIdx is operand index
		right[oIdx].setIndex(idx);
	}

	Operand getLeftOperand() const {
		return left;
	}
	const vector<Operand>& getRightOperand() const {
		return right;
	}
	string getOp() const {
		return op;
	}
	LeftOp getLeftOp() const {
		return lop;
	}
	Operand getRightOperand(int i) const {
		assert(size_t(i) < right.size());
		return right[i];
	}
};