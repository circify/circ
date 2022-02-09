#include <cassert>
#include <iostream>
#include <fstream>
#include <string>
#include <sys/stat.h>
#include <vector>
#include <bits/stdc++.h>

enum mode {
    mpc,
 };

mode hash(std::string m) {
    if (m == "mpc") return mpc;
    throw std::invalid_argument("Unknown mode: "+m);
}

std::vector<std::string> split(std::string str, char delimiter) {
    std::vector<std::string> result;
    std::istringstream ss(str);
    std::string word; 
    while (ss >> word) {
        result.push_back(word);
    }
    return result;
}

std::unordered_map<std::string, int> parse_mpc_inputs(std::string test_file_path, int role) {
    std::unordered_map<std::string, int> input_map;

    std::ifstream file(test_file_path);
    assert(("Test file exists.", file.is_open()));

    std::string str;
    bool role_flag = false;
    while (std::getline(file, str)) {
        std::vector<std::string> line = split(str, ' ');
        if (line.size() == 0) continue;
        if (line[0].rfind("// server", 0) == 0) {
            if (role == 0) role_flag = true;
            if (role == 1) role_flag = false;
            continue;
        }
        if (line[0].rfind("// client", 0) == 0) {
            if (role == 1) role_flag = true;
            if (role == 0) role_flag = false;
            continue;
        }
        if (role_flag) {
            if (line.size() == 2) {
                input_map[line[0]] = std::stoi(line[1]);
            } else if (line.size() > 2) {
                // Vector input, key_idx: value
                for (int i = 1; i < line.size(); i++) {
                    std::string key = line[0] + "_" + std::to_string(i-1);
                    input_map[line[0]] = std::stoi(line[i]);
                }
            }
        }
    }
    return input_map;
}

int main (int argc, char* argv[]) {
    
    std::vector<std::string> args(argv + 1, argv + argc);
    std::string m, test_file_path;
    for (auto i = args.begin(); i != args.end(); ++i) {
        if (*i == "-m" || *i == "--mode") {
            m = *++i;
        } else if (*i == "-t" || *i == "--test_file") {
            test_file_path = *++i;
        }
    }

    switch(hash(m)) {
        case mpc: {
            parse_mpc_inputs(test_file_path);
        }
        break;
    }
    return 0;
}