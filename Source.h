#pragma once
#include <string>
#include <map>
#include <fstream>
#include <iostream>
#include <iterator>
#include "Contract.h"
#include "AST.h"

#include "spdlog/spdlog.h"
#include "spdlog/sinks/stdout_color_sinks.h"

#include "rapidjson/document.h"
#include "rapidjson/istreamwrapper.h"
using namespace std;
extern string sol;
extern int validSolNum;

class Source {
	//friend rapidjson::Document;
protected:

private:
	string filePath;
	string fileContent;

	map<string, Contract> contracts;//contract name => contract object

	//vector<string> sourceList;//source .sol file list
	map<int, tuple<string, string>> sourceContents;
	string version;//compiler version
	rapidjson::Document combinedJson;

	//fileName => AST root Node
	map<string, const rapidjson::Value*> ASTs;
public:

	Source(string filePath) {
		this->filePath = filePath;
		setFileContent(filePath, fileContent);
	}
	void setFilePath(string filePath) { this->filePath = filePath; }
	const string& getFilePath() { return filePath; }

	void setCombinedJson(string solc, string filePath, string version, bool optimizeEnabled, int optimizeRuns, string evmVersion = "petersburg") {
		this->version = version;
		string jsonPath = filePath + ".json";
		string errPath = filePath + ".err";
		string optimize;
		if (optimizeEnabled)
			optimize += " --optimize --optimize-runs " + to_string(optimizeRuns);

		string cmd = solc + optimize + " --combined-json abi,ast,bin,bin-runtime,opcodes,srcmap,srcmap-runtime " + filePath + " 1> " + jsonPath + " 2> " + errPath;
		system(cmd.c_str());

		fstream fin;
		int ch;
		fin.open(jsonPath, ios::in);
		ch = fin.get();
		if (fin.eof() || ch == EOF) {
			cerr << "compile error : " << jsonPath << endl;
			cout << "c" << endl;
			return;
			//exit(-1);
		}
		fin.close();

		ifstream jsonFile(jsonPath);
		if (!jsonFile) {
			cerr << "Fail to open File : " << jsonPath << endl;
			exit(-1);
		}

		rapidjson::IStreamWrapper isw(jsonFile);
		combinedJson.ParseStream(isw);
	}
	const rapidjson::Document& getCombinedJson() { return combinedJson; }



	static void setFileContent(string filePath, string& fileContent) {
		ifstream contract(filePath, ios::in | ios::binary);
		if (!contract) {
			cerr << "Fail to open File : " << filePath << endl;
			exit(-1);
		}

		string content((std::istreambuf_iterator<char>(contract)), std::istreambuf_iterator<char>());
		fileContent = content;
	}
	const string& getFileContent() { return fileContent; }

	void parseCombinedJson() {
		if (!combinedJson.IsObject()) {
			cout << filePath << " compile error" << endl;
			return;
		}
		validSolNum += 1;
		const rapidjson::Value& contracts = combinedJson["contracts"];
		for (rapidjson::Value::ConstMemberIterator iter = contracts.MemberBegin(); iter != contracts.MemberEnd(); ++iter) {
			//关于contractName中路径分隔符是 / 还是 \ 的问题是由于solidity编译器决定的
			//^0.4.x 为 \
			//^0.5.x 为 /
			string contractName = iter->name.GetString();
			//cout << contractName << endl;
			const rapidjson::Value& combined = iter->value;

			string bin = combined["bin"].GetString();//deploy contains runtime code
			string binRuntime = combined["bin-runtime"].GetString();

			if (bin == "")//interface not a contract
				continue;
			if (boost::starts_with(binRuntime, "73"))//library not a contract
				continue;
			
			//0x0000000000dfed903ad76996fc07bf89c0127b1e为例：constructor不一定为bin - binRuntime,可能存在部分冗余
			string constructor = bin.substr(0, bin.length() - binRuntime.length());

			string runtime = binRuntime;



			string opcodes = combined["opcodes"].GetString();//generate both deploy and runtime opcodes at the same time
			string srcmap = combined["srcmap"].GetString();
			string srcmapRuntime = combined["srcmap-runtime"].GetString();
			Contract c(contractName, constructor, runtime, "", srcmap, srcmapRuntime, &fileContent, version);
			this->contracts.insert(pair<string, Contract>(contractName, c));
		}


		const rapidjson::Value& sourceList = combinedJson["sourceList"];
		int i = 0;
		for (rapidjson::Value::ConstValueIterator itr = sourceList.Begin(); itr != sourceList.End(); ++itr) {
			string filePath = itr->GetString();
			string fileContent;
			setFileContent(filePath, fileContent);
			sourceContents[i] = make_tuple(filePath, fileContent);
			i++;
		}

		for (auto& c : this->contracts)
			c.second.setSrcContens(&sourceContents);

		//const rapidjson::Value& sources = combinedJson["sources"];

		//for (rapidjson::Value::ConstMemberIterator iter = sources.MemberBegin(); iter != sources.MemberEnd(); ++iter) {
		//	const rapidjson::Value& ast = iter->value;
		//	//cout << iter->name.GetString() << endl;
		//	assert(iter->name.IsString());
		//	ASTs.insert(pair<string, const rapidjson::Value*>(string(iter->name.GetString()), &ast));
		//}

		//sol = fileContent;
		//for (auto& a : ASTs) {
		//	ASTNode* srcUnit = initFromJson(a.second);


		//	map<string, bool> loopInfo = hasLoop(srcUnit);
		//	for (auto& i : loopInfo)
		//		if (i.second)
		//			cout << srcUnit->name << " : " << i.first << " has LOOP" << endl;

		//	deleteAST(srcUnit);
		//}
	}

	const Contract& getContract(string contractName) {
		if (contracts.find(contractName) == contracts.end()) {
			cout << contractName << " not found" << endl;
			exit(-1);
		}

		//do not use contracts[contractName] because Contract has no default constructor
		return contracts.at(contractName);
	}
	const map<string, Contract>& getContracts() { return contracts; }
};