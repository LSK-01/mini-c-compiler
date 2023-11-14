#include "computeSets.hpp"
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <algorithm>
#include <vector>

std::string endOfFile = "0";
std::string cyclical = "_CYCLICAL";

bool nullable(const std::string& input, std::string current = "");
std::vector<std::string> splitString(const std::string& str, const std::string& delimiter);
std::unordered_set<std::string> first(const std::string& input);
std::unordered_set<std::string> follow(const std::string& input, std::unordered_set<std::string> visited = {});

std::unordered_map<std::string, std::unordered_set<std::string>> firstSets;
std::unordered_map<std::string, std::unordered_set<std::string>> followSets;
std::unordered_map<std::string, std::vector<std::vector<std::string>>> productions;

std::string removeCharacter(std::string str, char char_to_remove) {
    str.erase(std::remove(str.begin(), str.end(), char_to_remove), str.end());
    return str;
}

void removeQuotesFromSets(std::unordered_map<std::string, std::unordered_set<std::string>>& sets) {
    std::unordered_map<std::string, std::unordered_set<std::string>> updatedSets;

    for (auto& pair : sets) {
        // Remove quotes from key unless terminal
        std::string newKey = pair.first;
        if(!(pair.second.size() == 1 && pair.first == *pair.second.begin())){
          newKey = removeCharacter(pair.first, '"');
        }

        std::unordered_set<std::string> newSet;
        for (const std::string& value : pair.second) {
            // Remove quotes from each value in the set
            newSet.insert(removeCharacter(value, '"'));
        }

        // Insert the updated key and set into the new map
        updatedSets[newKey] = newSet;
    }

    // Replace the old map with the updated map
    sets = std::move(updatedSets);
}

void computeFirst() {
  for (const auto& prod : productions) {
    first(prod.first);
  }

  removeQuotesFromSets(firstSets);
}

void printFirst() {
  for (const auto& kv : firstSets) {
    std::cout << "FIRST(" << kv.first << ") = { ";

    for (const auto& value : kv.second) {
      std::cout << "'" + value + "'" << " ";
    }

    std::cout << "}" << std::endl;
  }
}

void sententialForms(std::string& input) {
  for (auto& prod : productions.find(input)->second) {
    // get last terminal, this can have eof
    std::string symbol = prod[prod.size() - 1];
    if (isTerminal(symbol)) {
      continue;
    }

    followSets[symbol].insert(endOfFile);
    if (symbol != input) {
      sententialForms(symbol);
    }
  }
}

void printFollow() {
  for (const auto& kv : followSets) {
    std::cout << "FOLLOW(" << kv.first << ") = { ";

    for (const auto& value : kv.second) {
      std::cout << "'" + value + "'" << " ";
    }

    std::cout << "}" << std::endl;
  }
}

void computeFollow() {
  for (const auto& prod : productions) {
    follow(prod.first);
  }

  for (const auto& pair : followSets) {
    std::unordered_set<std::string>& unordered_set = followSets[pair.first];

    for (auto it = unordered_set.begin(); it != unordered_set.end(); it++) {
      std::string elem = *it;
      if (elem.find(cyclical) != std::string::npos) {
        std::vector<std::string> parts = splitString(elem, ":");
        unordered_set.insert(followSets[parts[1]].begin(), followSets[parts[1]].end());
        unordered_set.erase(elem);

        if (unordered_set.empty()) {
          break;
        }
        it = unordered_set.begin();
      }
    }

    if (unordered_set.empty()) {
      unordered_set.insert(endOfFile);
      continue;
    }
  }
  // add EOFs
  std::string startVar = "program";
  followSets[startVar].insert(endOfFile);
  sententialForms(startVar);

  removeQuotesFromSets(followSets);
}

std::unordered_set<std::string> follow(const std::string& input, std::unordered_set<std::string> visited) {

  if (followSets.find(input) != followSets.end()) {
    return followSets.find(input)->second;
  }

  visited.insert(input);
  for (auto& prod : productions) {
    const std::string& nonterm = prod.first;
    for (auto& rule : prod.second) {
      for (int i = 0; i < rule.size(); i++) {

        const std::string& symbol = rule[i];
        if (symbol != input) {
          continue;
        }

        if (i + 1 == rule.size()) {

          if (visited.find(nonterm) == visited.end()) {
            std::unordered_set<std::string> followNonTerm = follow(nonterm, visited);
            if (followNonTerm.empty()) {
              followSets[symbol].insert("_CYCLICAL:" + nonterm);
            } else {
              followSets[symbol].insert(followNonTerm.begin(), followNonTerm.end());
            }
          } else {
            if (nonterm != symbol) {
              std::unordered_set<std::string> empty;
              return empty;
            }
            break;
          }
        } else {
          int adjCounter = i;
          std::string adj = rule[++adjCounter];

          if (isTerminal(adj)) {
            followSets[symbol].insert(adj);
          } else {
            followSets[symbol].insert(firstSets[adj].begin(), firstSets[adj].end());

            while (adjCounter < rule.size() - 1 && nullable(rule[adjCounter])) {
              adj = rule[++adjCounter];
              if (isTerminal(adj)) {
                followSets[symbol].insert(adj);
              } else {
                followSets[symbol].insert(firstSets[adj].begin(), firstSets[adj].end());
              }
            }

            // if everything to the right of this symbol was nullable, then also
            // add FOLLOW(input)
            if (adjCounter == rule.size() - 1 && nullable(rule[adjCounter])) {
              std::unordered_set<std::string> followNonTerm = follow(nonterm);
              followSets[symbol].insert(followNonTerm.begin(), followNonTerm.end());
              
            }
          }
        }

        followSets[symbol].erase("''");
      }
    }
  }
  return followSets[input];
}

std::unordered_set<std::string> first(const std::string& input) {
  if (firstSets.find(input) != firstSets.end()) {
    return firstSets.find(input)->second;
  }

  std::unordered_set<std::string> thisFirst;

  if (isTerminal(input)) {
    thisFirst = {input};
    firstSets[input] = thisFirst;
    return thisFirst;
  }

  auto find = productions.find(input);
  if (find == productions.end()) {
    std::cout << " (first) couldnt find: " + input << std::endl;
    return {};
  }

  for (auto& prod : find->second) {
    for (std::string symbol : prod) {

      std::unordered_set<std::string> symbolFirst = first(symbol);
      thisFirst.insert(symbolFirst.begin(), symbolFirst.end());

      // keep going while this symbol is nullable
      if (!nullable(symbol)) {
        break;
      } else {
        // we can add epsilon
        thisFirst.insert("''");
      }
    }
  }

  firstSets[input] = thisFirst;

  return thisFirst;
}

bool nullable(const std::string& input, std::string current) {
  if (current == input) {
    return false;
  }

  if (current == "") {
    current = input;
  }

  if (isTerminal(current)) {
    return false;
  }

  bool isThisNullable = true;
  bool isNullable = false;

  auto find = productions.find(current);
  if (find == productions.end()) {
    std::cout << "couldnt find: " + current << std::endl;
    return false;
  }

  for (auto& prod : find->second) {

    for (std::string symbol : prod) {

      // can go straight to epsilon
      if (symbol == "''" && prod.size() == 1) {
        isThisNullable = true;
      }
      // contains a terminal
      else if (isTerminal(symbol)) {
        isThisNullable = false;
      } else {
        isThisNullable = isThisNullable && nullable(input, symbol);
      }
    }

    isNullable |= isThisNullable;
  }

  return isNullable;
}

bool isTerminal(const std::string& str) {
  if (str == "''" || str.find("\"") != std::string::npos || std::isupper(str[0])) {
    return true;
  }

  return false;
}

std::vector<std::string> splitString(const std::string& str, const std::string& delimiter) {
  std::vector<std::string> result;
  size_t start = 0;
  size_t end = str.find(delimiter);

  while (end != std::string::npos) {
    result.push_back(str.substr(start, end - start));
    start = end + delimiter.length();
    end = str.find(delimiter, start);
  }

  result.push_back(str.substr(start, end));
  return result;
}

void printProductions(const std::unordered_map<std::string, std::vector<std::vector<std::string>>>& productions) {
  for (const auto& [input, rules] : productions) {
    std::cout << input << " ::= ";

    for (size_t i = 0; i < rules.size(); ++i) {
      const auto& rule = rules[i];
      for (const auto& symbol : rule) {
        std::cout << symbol << (isTerminal(symbol) ? "(T)" : "(NT)") << " ";
      }

      if (i != rules.size() - 1) {
        std::cout << "| ";
      }
    }

    std::cout << '\n';
  }
}

std::string trim(const std::string& str) {
  size_t start = str.find_first_not_of(" \t\n\r\f\v");
  size_t end = str.find_last_not_of(" \t\n\r\f\v");

  // If no non-whitespace found, return an empty string
  if (start == std::string::npos) {
    return "";
  }

  return str.substr(start, end - start + 1);
}

void readGrammar(std::string filename) {
  std::ifstream file(filename);
  std::string line;

  if (!file.is_open()) {
    std::cerr << "Failed to open the file.\n";
    return;
  }

  while (std::getline(file, line)) {
    if (line != "") {
      std::vector<std::string> parts = splitString(line, " ::= ");

      if (parts.size() < 2) {
        std::cerr << "Invalid line format: " << line << '\n';
        continue;
      }

      std::vector<std::string> rhsParts = splitString(trim(parts[1]), " ");
      std::string input = trim(parts[0]);
      // true if terminal
      std::vector<std::string> rhs;

      for (auto& part : rhsParts) {
        // terminals are either epsilon, surrounded by quotes, or start with an
        // uppercase character
        if (isTerminal(part)) {
          rhs.push_back(part);
        } else {
          rhs.push_back(part);
        }
      }

      productions[input].push_back(rhs);
    }
  }
  file.close();
}
