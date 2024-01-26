#include <bitset>
#include <sstream>
#include <valarray>
#include <vector>
#include "iostream"
#include "sha-3.h"
std::string parseMessageToBinary(std::string message) {
    std::ostringstream parsedMessageStream;
    for (char& c : message) {
        int asciiValue = static_cast<int>(c);
        std::string binaryString = std::bitset<8>(asciiValue).to_string();
        parsedMessageStream<<binaryString;
    }
    std::string parsedMessage = parsedMessageStream.str();
    return parsedMessage;
}
void padMessage(std::string & message) {
    message+='1';
    while(message.size() != R - 1) {
        message+='0';
    }
    message+='1';
}
std::vector<std::string> divideByParts(std::string binaryMessage) {
    std::vector<std::string> blocks;
    for(unsigned int i =0; i < binaryMessage.size();i+=R) {
        std::string block = binaryMessage.substr(i,R);
        blocks.push_back(block);
    }
    return blocks;
}

StateArray ***  createEmpty3DArray() {
    auto *** A = new StateArray ** [A_ARRAY_SIZE];
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        A[i] = new StateArray * [A_ARRAY_SIZE];
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            A[i][j] = new StateArray [W];
        }
    }
    return A;
}
StateArray **  createEmpty2DArray() {
    auto ** A = new StateArray * [A_ARRAY_SIZE];
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            A[i][j] = new StateArray [W];
        }
    }
    return A;
}
StateArray *** parseStateToArray(const std::bitset<BLOCK_SIZE>& state) {
    auto *** A = createEmpty3DArray();
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                unsigned int index = (A_ARRAY_SIZE * i + j) * W + k;
                bool bit = state[index];
                A[i][j][k] = bit;
            }
        }
    }
    return A;
}
std::string parseArrayToState(StateArray *** A) {
    std::string S;
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                S+=std::to_string(A[i][j][k]);
            }
        }
    }
    return S;
}
StateArray *** stepTheta(StateArray *** A) {
    auto ** c = new StateArray * [A_ARRAY_SIZE];
    auto ** d = new StateArray * [A_ARRAY_SIZE];
    for(unsigned int i = 0; i < A_ARRAY_SIZE; i++) {
        c[i] = new StateArray [W];
        for (unsigned int k = 0; k < W; ++k) {
            c[i][k]=A[i][0][k]^A[i][1][k]^A[i][2][k]^A[i][3][k]^A[i][4][k];
        }
    }
    for(unsigned int i = 0; i < A_ARRAY_SIZE; i++) {
        d[i] = new StateArray [W];
        for (unsigned int k = 0; k < W; ++k) {
            d[i][k]=c[(i-1)%5][k]^c[(i+1)%5][(k-1)%W];
        }
    }

    auto *** changedA = createEmpty3DArray();
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                changedA[i][j][k] ^= d[i][k];
            }
        }
    }
    return changedA;
}
StateArray *** stepRho(StateArray *** A) {
    auto *** changedA = createEmpty3DArray();
    for(unsigned int k = 0; k < W; k++) {
        changedA[0][0][k]=A[0][0][k];
    }
    unsigned int i = 1;
    unsigned int j = 0;
    for (unsigned int t = 0; t < T_ROUNDS; ++t) {
        for(unsigned int k = 0; k < W; k++) {
            changedA[i][j][k]=A[i][j][(k-(t+1)*(t+2)/2)%W];
        }
        unsigned int oldI = i;
        i = j;
        j = (2*oldI +3*j) % 5;
    }
    return changedA;
}
StateArray *** stepPi(StateArray *** A) {
    auto *** changedA = createEmpty3DArray();
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                changedA[i][j][k] = A[(i+3*j)%5][i][k];
            }
        }
    }
    return changedA;
}
StateArray *** stepChi(StateArray *** A) {
    auto *** changedA = createEmpty3DArray();
    for (int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                changedA[i][j][k] = A[i][j][k] ^ ((A[(i+1)%5][j][k]^1) * A[(i+2)%5][j][k]);
            }
        }
    }
    return changedA;
}
bool rc(unsigned int t) {
    unsigned int remainder = t % RC_MODULE;
    std::vector<bool> rArray = RC_R_ARRAY;
    if (remainder == 0) return 1;
    for(unsigned int i = 1; i < remainder; i++) {
        rArray.insert(rArray.begin(), 0);
        rArray[0] = rArray[0] ^ rArray[8];
        rArray[4] = rArray[4] ^ rArray[8];
        rArray[5] = rArray[5] ^ rArray[8];
        rArray[6] = rArray[6] ^ rArray[8];
        rArray.resize(8);
    }
    return rArray[0];
}
StateArray *** stepIota(StateArray *** A, unsigned int ir) {
    auto *** changedA = createEmpty3DArray();
    for(unsigned int i = 0; i < A_ARRAY_SIZE; ++i) {
        for (int j = 0; j < A_ARRAY_SIZE; ++j) {
            for (int k = 0; k < W; ++k) {
                changedA[i][j][k] = A[i][j][k];
            }
        }
    }
    bool RC[W];
    for (unsigned int i = 0; i < W; ++i) {
        RC[i] = 0;
    }
    for (unsigned int i = 0; i < L; ++i) {
        unsigned int rcIndex = pow(2,i)-1;
        RC[rcIndex] = rc(i+7*ir);
    }
    for (int k = 0; k < W; ++k) {
        changedA[0][0][k] = A[0][0][k] ^ RC[k];
    }
    return changedA;
}

std::bitset<BLOCK_SIZE> absorbMessage(std::vector<std::string> blocks) {
    std::bitset<BLOCK_SIZE> S (std::string(BLOCK_SIZE,'0'));
    StateArray *** A = parseStateToArray(S);
    for(auto & block : blocks) {
        while (block.size() != BLOCK_SIZE) {
            block.push_back('0');
        }
        std::bitset<BLOCK_SIZE> blockBitset(block);
        S = blockBitset ^ S;
        A = parseStateToArray(S);
        for (unsigned int i = 0; i < ROUNDS_AMOUNT; ++i) {
            A = stepIota(stepChi(stepPi(stepRho(stepTheta(A)))),i);
        }
        std::string parsedState = parseArrayToState(A);
        std::reverse(parsedState.begin(), parsedState.end());
        S = std::bitset<BLOCK_SIZE>(parsedState);
    }
    return S;
}
std::bitset<OUTPUT_LENGTH> squeezeMessage(std::bitset<BLOCK_SIZE> S) {
    std::bitset<OUTPUT_LENGTH> result;
    for (int i = 0; i < OUTPUT_LENGTH; ++i) {
        result[i] = S[i];
    }
    return result;
}
std::string SHA3(std::string initialMessage) {
    std::string message = parseMessageToBinary(initialMessage);
    padMessage(message);
    std::vector<std::string> blocks = divideByParts(message);
    std::cout<<squeezeMessage(absorbMessage(blocks));
    return "";
}
int main() {
    std::string message="abcde";
    SHA3(message);
    return 0;
}
