#include "global.h"
#include "spdlog/common.h"
#ifdef _WIN32
#include <windows.h>
#endif
#include <iostream>
using namespace std;

void displayRedMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[31m" << msg << "\033[0m" << endl;
#endif
}
void displayBlueMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_BLUE | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[34m" << msg << "\033[0m" << endl;
#endif
}
void displayGreenMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_GREEN | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[32m" << msg << "\033[0m" << endl;
#endif
}
void displayYellowMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[33m" << msg << "\033[0m" << endl;
#endif
}

void displayCyanMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_BLUE | FOREGROUND_GREEN | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[36m" << msg << "\033[0m" << endl;
#endif
}

void displayPurpleMsg(const string& msg) {
#ifdef _WIN32
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_BLUE | FOREGROUND_RED | FOREGROUND_INTENSITY);
	cout << msg << endl;
	SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#endif
#ifdef __linux__
	cout << "\033[35m" << msg << "\033[0m" << endl;
#endif
}

void displayRedMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayRedMsg(msg);
}
void displayBlueMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayBlueMsg(msg);
}
void displayGreenMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayGreenMsg(msg);
}
void displayYellowMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayYellowMsg(msg);
}
void displayCyanMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayCyanMsg(msg);
}
void displayPurpleMsg(const string& msg, spdlog::level::level_enum level) {
	if (LOG_LEVEL == level)
		displayPurpleMsg(msg);
}