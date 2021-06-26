#pragma once
//#define LOG_LEVEL spdlog::level::info
//#define LOG_LEVEL spdlog::level::info
#define LOG_LEVEL spdlog::level::off
#include <string>
#ifdef _WIN32
#define SSCANF sscanf_s
#endif
#ifdef __linux__
#define SSCANF sscanf
#endif
bool isNumerical(std::string s);
bool isLowercaseHex(std::string s);

void displayRedMsg(const std::string& s);
void displayBlueMsg(const std::string& s);
void displayGreenMsg(const std::string& s);
void displayYellowMsg(const std::string& s);
void displayPurpleMsg(const std::string& s);
void displayCyanMsg(const std::string& s);