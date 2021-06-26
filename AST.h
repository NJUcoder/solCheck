#pragma once
#include<string>
#include<vector>
#include <map>
#include <iostream>
#include "rapidjson/document.h"
#include "rapidjson/istreamwrapper.h"
using namespace std;
class ASTNode {
private:

public:
	static rapidjson::Value null;
	int id;
	string name;
	string src;
	const rapidjson::Value& attr;
	vector<ASTNode*> children;

	void addChild(ASTNode* node);

	ASTNode(int id, string name, string src, const rapidjson::Value& attr) :id(id), name(name), src(src), attr(attr) {}
};

//"sources" => "for.sol" => "AST" => {"attributes(optional), id, name(SourceUnit), src, children(optional)"}
ASTNode* initFromJson(const rapidjson::Value* solName);//solName对应的Value
void init(const rapidjson::Value& info, ASTNode* father);
map<string, bool> hasLoop(ASTNode* srcUnit);//从源代码角度，而不通过程序控制流图
bool hasLoopStatement(ASTNode* node);
void deleteAST(ASTNode* srcUnit);