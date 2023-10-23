#pragma once
#include <unordered_map>
#include <unordered_set>
#include <string>   
#include <vector>
#include <cstdlib>

void computeFirst();
void printFirst();
void printFollow(); 
void computeFollow();
void readGrammar(std::string filename);
bool isTerminal(const std::string& str);

extern std::unordered_map<std::string, std::unordered_set<std::string>> firstSets;
extern std::unordered_map<std::string, std::unordered_set<std::string>> followSets;
extern std::unordered_map<std::string, std::vector<std::vector<std::string>>> productions;