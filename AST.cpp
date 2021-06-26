#include "AST.h"
#include <boost/algorithm/algorithm.hpp>
#include <boost/algorithm/string.hpp>
#include "global.h"
rapidjson::Value ASTNode::null;
void init(const rapidjson::Value& info, ASTNode* father) {
	//cout << info["id"].GetInt()<< " " << info["name"].GetString() << endl;
	ASTNode* nPtr;
	if (info.HasMember("attributes"))
		nPtr = new ASTNode(info["id"].GetInt(), string(info["name"].GetString()), string(info["src"].GetString()), info["attributes"]);
	else
		nPtr = new ASTNode(info["id"].GetInt(), string(info["name"].GetString()), string(info["src"].GetString()), ASTNode::null);
	father->addChild(nPtr);
	if (!info.HasMember("children"))//leaf node has no "children" object array
		return;
	for (auto& c : info["children"].GetArray()) {
		init(c, nPtr);
	}
}
void ASTNode::addChild(ASTNode* node) {
	children.push_back(node);
}
ASTNode* initFromJson(const rapidjson::Value* astObj) {
	const rapidjson::Value& astVal = (*astObj)["AST"];
	ASTNode* srcUint = new ASTNode(astVal["id"].GetInt(), string(astVal["name"].GetString()), string(astVal["src"].GetString()), astVal["attributes"]);
	//const rapidjson::Value& attr = astVal["attributes"];
	const rapidjson::Value& children = astVal["children"];
	for (auto& c : children.GetArray()) {
		init(c, srcUint);
	}
	return srcUint;
}
void deleteAST(ASTNode* node) {
	for (auto n : node->children)
		deleteAST(n);
	delete node;
}

string sol;
int num = 0;//循环后有后置条件
int loop = 0;//检测到了的循环（目前怀疑可能有漏报）
int simpleForLoop = 0;
//int contractNum = 0;
bool postCondExists(int loopEnd, string sol) {
	string content;
	for (size_t i = loopEnd; i < sol.size(); i++)
		if (sol[i] == '\n' || sol[i] == '\r') {
			if (!content.empty())
				break;
		}
		else
			content.push_back(sol[i]);
	if (content.find("assert") != string::npos) {
		displayGreenMsg(content);
		return true;
	}
	else
		return false;
}
string getSrcContent(ASTNode* node, const string& sol) {
	string srcmap = node->src;
	vector<string> temp;
	boost::split(temp, srcmap, boost::is_any_of(":"));
	int start = stoi(temp[0]);
	int length = stoi(temp[1]);
	num += postCondExists(start + length, sol);
	//cout << postCondExists(start + length, sol) << endl;
	return sol.substr(start, length);
}
string getSrcContentFirstLine(string& loop) {
	string res;
	for (size_t i = 0; i < loop.length(); i++) {
		if (loop[i] == '\r' || loop[i] == '\n')
			break;
		res.push_back(loop[i]);
	}
	return res;
}
map<string, bool> hasLoop(ASTNode* root) {//从源代码角度，而不通过程序控制流图
	assert(root->name == "SourceUnit");
	map<string, bool> conLoopInfo;
	for (auto& c : root->children)
		if (c->name == "ContractDefinition") {
			string contractName = c->attr["name"].GetString();
			//cout << getSrcContent(c, sol) << endl;
			conLoopInfo[contractName] = hasLoopStatement(c);
		}
	return conLoopInfo;
}



bool hasLoopStatement(ASTNode* node) {
	if (node->name == "WhileStatement" ||
		node->name == "ForStatement" ||
		node->name == "DoWhileStatement" ||
		node->name == "AssemblyForLoop"
		) {
		loop++;
		string loopContent = getSrcContent(node, sol);
		string firstLine = getSrcContentFirstLine(loopContent);
		if (firstLine.find("for") != string::npos && (firstLine.find("++") != string::npos || firstLine.find("--") != string::npos))
			simpleForLoop++;
		displayRedMsg(loopContent);

		return true;
	}
	else if (node->children.empty())
		return false;
	else {
		bool res = false;
		for (auto& c : node->children)
			res = hasLoopStatement(c) || res;
		//res = res || hasLoopStatement(c);
		return res;
	}
}