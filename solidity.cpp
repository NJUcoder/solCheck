#include "Source.h"
#include "Contract.h"
#include <algorithm>
#include <time.h>
#ifdef __linux__
#include <dirent.h>
#include <sys/types.h>
#endif
namespace spd = spdlog;
namespace z = z3;
using namespace std;

std::shared_ptr<spdlog::logger> console = spdlog::stdout_color_mt("solidity front");

//A class's static variable should be initialized
map<string, int> Opcode::opcodes;
map<int, tuple<int, int>> Opcode::operations;
map<int, string> Opcode::mnemonics;
map<string, CostType> Opcode::costTypes;
map<CostType, int> Opcode::costs;
set<string> Opcode::memOpcodes;
//map<string, int> StackFrame::exprDepth;
void genBytecode(const map<int, string>& instrs, string& bytecode);

int ECFGNode::count = 0;
int Operand::num8 = 0;
int Operand::num256 = 0;
int Operand::num512 = 0;
int Transition::tran_id = 0;
z3::context StackFrame::c;
bool isNumerical(string s) {
	for (auto c : s)
		if (c > '9' || c < '0')
			return false;
	return true;
}
bool isLowercaseHex(string s) {
	for (auto& c : s)
		if (c >= '0' && c <= '9' || c >= 'a' && c <= 'f')
			continue;
		else
			return false;
	return true;
}
string solcdir = "D:\\solc";
void generateCFG(string solFile, string version) {
	Opcode::init();
	console->set_level(LOG_LEVEL);
	Source sol(solFile);
	sol.setCombinedJson(solcdir + "\\solc-" + version + ".exe", solFile, version, true, 200);
	//sol.setCombinedJson("..\\solidity-windows\\solc.exe", solFile);solcV = "0.5.8";
	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		string contractName = c.second.getName();
		cout << contractName << endl;

		//c.second.init();
		clock_t start;
		start = clock();
		c.second.genRuntimeByteCFG();
		if (c.second.isRecursive)
			continue;
		double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
		c.second.assertAnalysis();
		duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
	}
}
extern int num;
extern int loop;
extern int simpleForLoop;
int validSolNum = 0;

#ifdef _WIN32
void getFiles(std::string fileFolderPath, std::string fileExtension, std::vector<std::string>& file)
{
	std::string fileFolder = fileFolderPath + "\\*" + fileExtension;
	std::string fileName;
	struct _finddata_t fileInfo;
	long long findResult = _findfirst(fileFolder.c_str(), &fileInfo);
	if (findResult == -1) {
		_findclose(findResult);
		return;
	}
	do {
		fileName = fileFolderPath + "\\" + fileInfo.name;
		if (fileInfo.attrib == _A_ARCH)
			file.push_back(fileName);
	} while (_findnext(findResult, &fileInfo) == 0);
	_findclose(findResult);
}
#endif

#ifdef __linux__
void getFiles(std::string path, std::string fileExtension, std::vector<std::string>& filenames) {
	DIR* pDir;
	struct dirent* ptr;
	if (!(pDir = opendir(path.c_str())))
		return;
	while ((ptr = readdir(pDir)) != 0) {
		std::string tempFileName(ptr->d_name);
		if (tempFileName.size() >= 4 && tempFileName.substr(tempFileName.size() - 4) == ".sol")
			filenames.push_back(path + "/" + tempFileName);
	}
	closedir(pDir);
}
#endif

void genSpecialOffsets(map<string, tuple<int, int>>& res) {
	string allValidAddrTxtPath = "D:\\test\\allValidAddr.txt";
	ifstream special(allValidAddrTxtPath);
	if (!special) {
		cerr << "Fail to open " << allValidAddrTxtPath << endl;
		exit(-1);
	}
	string line;
	while (getline(special, line)) {
		vector<string> temp;
		boost::split(temp, line, boost::is_any_of(" "));
		res[temp[0]] = make_tuple(stoi(temp[1]), stoi(temp[2]));
	}
}

//constructorSize 为constructor的字符串长度（这里的constructor包含末尾多余的fe或者00指令）
//codeSize 为constructor和runtime的字符串长度之和（这里的runtime不包含末尾的fe或者00指令）
void assertExperimentWithoutSrc(string address, int constructorSize, int codeSize) {
	displayGreenMsg(address);
	Opcode::init();
	string rootDir = "D:\\test\\contracts\\" + address;
	string binPath = rootDir + "\\bin";
	ifstream binFile(binPath);
	string bin;
	getline(binFile, bin);

	string constructor = bin.substr(0, constructorSize);
	string cleanRuntime = bin.substr(constructorSize, codeSize - constructorSize);
	string left = bin.substr(codeSize);

	Contract c(rootDir + "\\" + address + ":", constructor, cleanRuntime, left, "", "", NULL, "");
	clock_t start = clock();
	c.setAddress(address);
	c.genRuntimeByteCFG();
	double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
	cout << duration << " seconds" << endl;
	if (c.isRecursive)
		return;

	c.assertAnalysis();
	duration = (double)(clock() - start) / CLOCKS_PER_SEC;
	cout << duration << " seconds" << endl;
}

void assertExperimentWithoutSrc(string address) {
	map<string, tuple<int, int>> res;
	genSpecialOffsets(res);
	int constructorSize = get<0>(res.at(address));//constructor length
	int codeSize = get<1>(res.at(address));//constructor length + cleanRuntimeBytecode length
	assertExperimentWithoutSrc(address, constructorSize, codeSize);
	cout << "successfully exit" << endl;
}

//constructorSize 为constructor的字符串长度（这里的constructor包含末尾多余的fe或者00指令）
//codeSize 为constructor和runtime的字符串长度之和（这里的runtime不包含末尾的fe或者00指令）
void sloadExperimentWithoutSrc(string address, int constructorSize, int codeSize) {
	displayGreenMsg(address);
	Opcode::init();
	string rootDir = "D:\\test\\contracts\\" + address;
	string binPath = rootDir + "\\bin";
	ifstream binFile(binPath);
	string bin;
	getline(binFile, bin);

	string constructor = bin.substr(0, constructorSize);
	string cleanRuntime = bin.substr(constructorSize, codeSize - constructorSize);
	string left = bin.substr(codeSize);

	Contract c(rootDir + "\\" + address + ":", constructor, cleanRuntime, left, "", "", NULL, "");
	clock_t start = clock();
	c.setAddress(address);
	c.genRuntimeByteCFG();
	double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
	cout << duration << " seconds" << endl;
	if (c.isRecursive)
		return;

	c.sloadAnalysis();
	duration = (double)(clock() - start) / CLOCKS_PER_SEC;
	cout << duration << " seconds" << endl;
}

void sloadExperimentWithoutSrc(string address) {
	map<string, tuple<int, int>> res;
	genSpecialOffsets(res);
	int constructorSize = get<0>(res.at(address));//constructor length
	int codeSize = get<1>(res.at(address));//constructor length + cleanRuntimeBytecode length
	sloadExperimentWithoutSrc(address, constructorSize, codeSize);
	cout << "successfully exit" << endl;
}


void assertAndSloadExperimentWithoutSrc(string address) {
	map<string, tuple<int, int>> res;
	genSpecialOffsets(res);
	int constructorSize = get<0>(res.at(address));//constructor length
	int codeSize = get<1>(res.at(address));//constructor length + cleanRuntimeBytecode length
	displayGreenMsg(address);
	Opcode::init();
	string rootDir = "D:\\test\\contracts\\" + address;
	string binPath = rootDir + "\\bin";
	ifstream binFile(binPath);
	string bin;
	getline(binFile, bin);

	string constructor = bin.substr(0, constructorSize);
	string cleanRuntime = bin.substr(constructorSize, codeSize - constructorSize);
	string left = bin.substr(codeSize);

	Contract c(rootDir + "\\" + address + ":", constructor, cleanRuntime, left, "", "", NULL, "");
	clock_t start = clock();
	c.setAddress(address);
	c.genRuntimeByteCFG();
	double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
	cout << duration << " seconds" << endl;
	if (!c.isRecursive) {
		c.assertAndSloadAnalysis();
		duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << " seconds" << endl;
	}
	cout << "successfully exit" << endl;
}

void sloadExperiment(string address) {
	string dir = "D:\\test\\contracts\\" + address;
	string info = dir + "\\info";
	ifstream infoFile(info);
	rapidjson::IStreamWrapper isw(infoFile);
	rapidjson::Document infoJson;
	infoJson.ParseStream(isw);
	string name = infoJson["name"].GetString();
	string version = infoJson["version"].GetString();
	int fileNo = infoJson["no"].GetInt();
	string optimize = infoJson["optimization"].GetString();
	vector<string> opInfo;
	boost::split(opInfo, optimize, boost::is_any_of(" "));
	bool optimizeEnabled = opInfo[0] == "Yes" ? true : false;
	int optimizeRuns = stoi(opInfo[2]);
	string settings = infoJson["settings"].GetString();
	size_t blankIdx = settings.find(" ");
	string evmVersion = settings.substr(0, blankIdx);
	string solFile;

	if (version[6] >= '0' && version[6] <= '9')
		version = version.substr(1, 6);
	else
		version = version.substr(1, 5);

	if (version == "0.4.15")
		return;
	string solc = solcdir + "\\solc-" + version + ".exe";

	assert(fileNo > 0);
	if (fileNo > 1) {//合约名与文件名不一定一致
		vector<string> files;
		getFiles(dir, ".sol", files);
		for (auto& filePath : files) {
			string tempFile = "temp.txt";
			string cmd = solc + " --bin-runtime " + filePath + " 1> " + tempFile;
			system(cmd.c_str());
			ifstream result(tempFile, ios::in);
			if (!result) {
				cerr << "Fail to open File : " << filePath << endl;
				exit(-1);
			}
			string content((std::istreambuf_iterator<char>(result)), std::istreambuf_iterator<char>());

			vector<string> temp;
			boost::split(temp, content, boost::is_any_of("\n"));
			for (auto& s : temp)
				if (!s.empty() && s[0] == '=') {
					s.erase(remove_if(s.begin(), s.end(), [](char c)->bool {return c == '=' || c == ' '; }), s.end());
					string contractName = s.substr(s.find_last_of(':') + 1);
					if (contractName == name) {
						solFile = filePath;
						break;
					}
				}
			if (!solFile.empty())break;
		}
		//solFile = dir + "\\" + name + ".sol";
	}
	else
		solFile = dir + "\\" + address + ".sol";
	Opcode::init();
	console->set_level(LOG_LEVEL);
	Source sol(solFile);
	sol.setCombinedJson(solcdir + "\\solc-" + version + ".exe", solFile, version, optimizeEnabled, optimizeRuns, evmVersion);
	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		string contract = c.second.getName();
		string contractName = contract.substr(contract.find_last_of(':') + 1);
		if (contractName != name)
			continue;

		clock_t start;
		start = clock();
		c.second.setAddress(address);
		c.second.genRuntimeByteCFG();
		if (c.second.isRecursive)
			continue;
		double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
		c.second.sloadAnalysis();
		duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
	}
}
void genCFG(string address, int constructorSize, int codeSize) {
	displayGreenMsg(address);
	Opcode::init();
	string binPath = "C:\\Users\\ASUS\\Desktop\\test\\contracts\\" + address + "\\bin";
	ifstream binFile(binPath);
	string bin;
	getline(binFile, bin);

	string constructor = bin.substr(0, constructorSize);
	string cleanRuntime = bin.substr(constructorSize, codeSize - constructorSize);
	string left = bin.substr(codeSize);

	Contract c("C:\\Users\\ASUS\\Desktop\\test\\contracts\\" + address + "\\" + address + ":", constructor, cleanRuntime, left, "", "", NULL, "");
	clock_t start = clock();
	c.setAddress(address);
	c.genRuntimeByteCFG();
	if (c.isRecursive)
		return;
}
void genCFGWithSrc(string address) {
	displayGreenMsg(address);
	string dir = "C:\\Users\\Siyuan Shen\\Desktop\\test\\contracts\\" + address;
	string info = dir + "\\info";
	ifstream infoFile(info);
	rapidjson::IStreamWrapper isw(infoFile);
	rapidjson::Document infoJson;
	infoJson.ParseStream(isw);
	string name = infoJson["name"].GetString();
	string version = infoJson["version"].GetString();
	int fileNo = infoJson["no"].GetInt();
	string optimize = infoJson["optimization"].GetString();
	vector<string> opInfo;
	boost::split(opInfo, optimize, boost::is_any_of(" "));
	bool optimizeEnabled = opInfo[0] == "Yes" ? true : false;
	int optimizeRuns = stoi(opInfo[2]);
	string settings = infoJson["settings"].GetString();
	size_t blankIdx = settings.find(" ");
	string evmVersion = settings.substr(0, blankIdx);
	string solFile;

	if (version[6] >= '0' && version[6] <= '9')
		version = version.substr(1, 6);
	else
		version = version.substr(1, 5);

	if (version == "0.4.15")
		return;
	string solc = solcdir + "\\solc-" + version + ".exe";

	assert(fileNo > 0);
	if (fileNo > 1) {//合约名与文件名不一定一致
		vector<string> files;
		getFiles(dir, ".sol", files);
		for (auto& filePath : files) {
			string tempFile = "temp.txt";
			string cmd = solc + " --bin-runtime " + filePath + " 1> " + tempFile;
			system(cmd.c_str());
			ifstream result(tempFile, ios::in);
			if (!result) {
				cerr << "Fail to open File : " << filePath << endl;
				exit(-1);
			}
			string content((std::istreambuf_iterator<char>(result)), std::istreambuf_iterator<char>());

			vector<string> temp;
			boost::split(temp, content, boost::is_any_of("\n"));
			for (auto& s : temp)
				if (!s.empty() && s[0] == '=') {
					s.erase(remove_if(s.begin(), s.end(), [](char c)->bool {return c == '=' || c == ' '; }), s.end());
					string contractName = s.substr(s.find_last_of(':') + 1);
					if (contractName == name) {
						solFile = filePath;
						break;
					}
				}
			if (!solFile.empty())break;
		}
		//solFile = dir + "\\" + name + ".sol";
	}
	else
		solFile = dir + "\\" + address + ".sol";

	Opcode::init();
	console->set_level(LOG_LEVEL);
	if (solFile == "")
		return;
	Source sol(solFile);
	sol.setCombinedJson(solc, solFile, version, optimizeEnabled, optimizeRuns, evmVersion);
	string jsonPath = solFile + ".json";
	fstream fin;
	int ch;
	fin.open(jsonPath, ios::in);
	ch = fin.get();
	if (fin.eof() || ch == EOF) {
		return;
	}
	fin.close();

	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		string contract = c.second.getName();
		string contractName = contract.substr(contract.find_last_of(':') + 1);
		if (contractName != name)
			continue;

		clock_t start;
		start = clock();
		c.second.setAddress(address);
		c.second.genRuntimeByteCFG();
		if (c.second.isRecursive)
			continue;
	}
}
void assertExperiment(string address) {
	displayGreenMsg(address);
	//string dir = "D:\\SolidityExperiments\\contracts\\" + address;
	//string dir = "D:\\Experiments\\contracts\\" + address;
	string dir = "D:\\test\\contracts\\" + address;
	//string dir = "contracts\\" + address;
	string info = dir + "\\info";
	ifstream infoFile(info);
	rapidjson::IStreamWrapper isw(infoFile);
	rapidjson::Document infoJson;
	infoJson.ParseStream(isw);
	string name = infoJson["name"].GetString();
	string version = infoJson["version"].GetString();
	int fileNo = infoJson["no"].GetInt();
	string optimize = infoJson["optimization"].GetString();
	vector<string> opInfo;
	boost::split(opInfo, optimize, boost::is_any_of(" "));
	bool optimizeEnabled = opInfo[0] == "Yes" ? true : false;
	int optimizeRuns = stoi(opInfo[2]);
	string settings = infoJson["settings"].GetString();
	size_t blankIdx = settings.find(" ");
	string evmVersion = settings.substr(0, blankIdx);
	string solFile;

	if (version[6] >= '0' && version[6] <= '9')
		version = version.substr(1, 6);
	else
		version = version.substr(1, 5);

	if (version == "0.4.26" || version == "0.5.16" || version == "0.4.15") {
		//version = "0.4.25";
		return;
	}
	string solc = solcdir + "\\solc-" + version + ".exe";

	assert(fileNo > 0);
	if (fileNo > 1) {//合约名与文件名不一定一致
		vector<string> files;
		getFiles(dir, ".sol", files);
		for (auto& filePath : files) {
			string tempFile = "temp.txt";
			string cmd = solc + " --bin-runtime " + filePath + " 1> " + tempFile;
			system(cmd.c_str());
			ifstream result(tempFile, ios::in);
			if (!result) {
				cerr << "Fail to open File : " << filePath << endl;
				exit(-1);
			}
			string content((std::istreambuf_iterator<char>(result)), std::istreambuf_iterator<char>());

			vector<string> temp;
			boost::split(temp, content, boost::is_any_of("\n"));
			for (auto& s : temp)
				if (!s.empty() && s[0] == '=') {
					s.erase(remove_if(s.begin(), s.end(), [](char c)->bool {return c == '=' || c == ' '; }), s.end());
					string contractName = s.substr(s.find_last_of(':') + 1);
					if (contractName == name) {
						solFile = filePath;
						break;
					}
				}
			if (!solFile.empty())break;
		}
		//solFile = dir + "\\" + name + ".sol";
	}
	else
		solFile = dir + "\\" + address + ".sol";

	Opcode::init();
	console->set_level(LOG_LEVEL);
	if (solFile == "")
		return;
	Source sol(solFile);
	sol.setCombinedJson(solc, solFile, version, optimizeEnabled, optimizeRuns, evmVersion);
	string jsonPath = solFile + ".json";
	fstream fin;
	int ch;
	fin.open(jsonPath, ios::in);
	ch = fin.get();
	if (fin.eof() || ch == EOF) {
		return;
	}
	fin.close();

	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		string contract = c.second.getName();
		string contractName = contract.substr(contract.find_last_of(':') + 1);
		if (contractName != name)
			continue;

		clock_t start;
		start = clock();
		c.second.setAddress(address);
		c.second.genRuntimeByteCFG();
		if (c.second.isRecursive)
			continue;
		double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
		//c.second.assertAnalysis();
		duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << duration << endl;
	}
}

void genConstructorInstrs(string address) {
	Opcode::init();
	string dir = "C:\\Users\\ASUS\\Desktop\\test\\contracts\\" + address;
	ifstream conFile(dir + "\\constructor");
	string constructor;
	getline(conFile, constructor);
	map<int, string> instrs;
	Contract::genInstrs(constructor, instrs);

	ofstream conInstrs(dir + "\\constructor.instrs");
	for (auto& i : instrs)
		conInstrs << i.first << " " << i.second << endl;
	conInstrs.close();
}
void genCleanRuntimeInstrs(string address) {
	Opcode::init();
	string dir = "D:\\test\\contracts\\" + address;
	ifstream cleanRuntimeFile(dir + "\\cleanRuntime");
	string runtime;
	getline(cleanRuntimeFile, runtime);
	map<int, string> instrs;
	Contract::genInstrs(runtime, instrs);

	ofstream cleanRuntimeInstrs(dir + "\\cleanRuntime.instrs");
	for (auto& i : instrs)
		cleanRuntimeInstrs << i.first << " " << i.second << endl;
	cleanRuntimeInstrs.close();
}

void genInstrs(string address, string bytecodeFileName, string instrFileName) {
	Opcode::init();
	string dir = "D:\\test\\contracts\\" + address;
	ifstream bytecodeFile(dir + "\\" + bytecodeFileName);
	string bytecode;
	getline(bytecodeFile, bytecode);
	map<int, string> instrs;
	Contract::genInstrs(bytecode, instrs);

	ofstream instrFile(dir + "\\" + instrFileName);
	for (auto& i : instrs)
		instrFile << i.first << " " << i.second << endl;
	instrFile.close();
}

string extractSolcName(string version){
	string solcName;
	string listJsonPath = "solc/list.json";
	ifstream jsonFile(listJsonPath);
	if (!jsonFile) {
		cerr << "Fail to open File : " << listJsonPath << endl;
		exit(-1);
	}
	rapidjson::IStreamWrapper isw(jsonFile);
	rapidjson::Document ltJson;
	ltJson.ParseStream(isw);

	const rapidjson::Value& builds = ltJson["builds"];
	for(auto& v : builds.GetArray()){
		//const rapidjson::Value& infos = iter->value;
		if(version == v["version"].GetString()){
			solcName = v["path"].GetString();
			//cout << solcName << endl;
			return solcName;
		}
	}

	cout << "Wrong solc version" <<endl;
	exit(-1);
}

void bytecodeOptimize(int opType, string solFile, string contractName, string version, bool optimizeEnabled = true, int optimizeRuns = 200){
	Opcode::init();
	console->set_level(LOG_LEVEL);
	Source sol(solFile);
	string solcExe = "solc/" + extractSolcName(version);
	sol.setCombinedJson(solcExe, solFile, version, optimizeEnabled, optimizeRuns);
	//sol.setCombinedJson("..\\solidity-windows\\solc.exe", solFile);solcV = "0.5.8";
	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		vector<string> temp;
		boost::split(temp, c.second.getName(), boost::is_any_of(":"));
		if (contractName != temp.back())
			continue;
		cout << contractName << endl;

		//c.second.init();
		clock_t start;
		start = clock();
		c.second.genRuntimeByteCFG();
		if (c.second.isRecursive)
			continue;
		double duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << "CFG construction time " << duration << " s" << endl;
		switch (opType)
		{
		case 1:c.second.assertAnalysis(); break;
		case 2:c.second.sloadAnalysis(); break;
		case 3:c.second.assertAndSloadAnalysis(); break;
		default:cout << "Wrong opType" << endl; break;
		}
		//c.second.assertAnalysis();
		duration = (double)(clock() - start) / CLOCKS_PER_SEC;
		cout << "Total time " << duration << " s" << endl;
	}
}

void buildVerFront(string solFile, string contractName, string version, bool optimizeEnabled = true, int optimizeRuns = 200) {
	Opcode::init();
	console->set_level(LOG_LEVEL);
	Source sol(solFile);
	string solcExe = "solc/" + extractSolcName(version);
	sol.setCombinedJson(solcExe, solFile, version, optimizeEnabled, optimizeRuns);
	sol.parseCombinedJson();
	map<string, Contract> contracts = sol.getContracts();
	for (auto& c : contracts) {
		vector<string> temp;
		boost::split(temp, c.second.getName(), boost::is_any_of(":"));
		if (contractName != temp.back())
			continue;
		else if (c.second.isRecursive) {
			cout << "There is a recursive function in the contract to be detected" << endl;
			break;
		}
		else {
			c.second.genRuntimeByteCFG();
			c.second.buildVerFront();
		}
	}
}

int main(int argc, char** argv)
{
	assert(argc >= 4 && argc <= 6);
	bool optimizeEnabled = true;
	int optimizeRuns = 200;
	if(argc >= 5){
		string t(argv[4]);
		assert(t == "true" || t == "false" || t == "t" || t == "f" || t == "T" || t == "F");
		if(t == "false" || t == "f" || t == "F")
			optimizeEnabled = false;
		if(argc == 6) {
			optimizeRuns = atoi(argv[5]);
		}
	}
	buildVerFront(argv[1], argv[2], argv[3], optimizeEnabled, optimizeRuns);
}
