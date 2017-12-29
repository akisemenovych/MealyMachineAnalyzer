#include <iostream>
#include <map>
#include <vector>
#include <queue>
#include <utility>
#include <fstream>

using namespace std;

class Expression {

private:

	string expressionHolder;

public:
	string getExpression() {
		return expressionHolder;
	}

	void setExpression(string expression) {
		expressionHolder = expression;
	}

	void concat(string part) {
		//size_t found = part.find("NULL");
		bool partNULLState = (part.find("NULL") != string::npos);
		bool partEPSState = (part.find("EPS") != string::npos);

		if (expressionHolder == "NULL") {
			return;
		}
		else if (expressionHolder == "EPS") {
			expressionHolder = part;
		}
		else if (!partNULLState && !partEPSState) {
			bool a = (expressionHolder.find(" v ") != string::npos);
			bool b = (part.find(" v ") != string::npos);

			if (a) {
				if (b)
					expressionHolder = "(" + expressionHolder + ")(" + part + ")";
				else
					expressionHolder = "(" + expressionHolder + ")" + part;
			}
			else {
				if (b) 
					expressionHolder += "(" + part + ")";
				else
					expressionHolder += part;
			}
		}/
	}

	void concat(Expression part) {
		this->concat(part.getExpression());
	}

	void unite(string part) {
		if (part == expressionHolder)
			return;

		bool partNULLState = (part.find("NULL") != string::npos);
		bool partEPSState = (part.find("EPS") != string::npos);

		if (expressionHolder == "NULL" || expressionHolder == "EPS")
			expressionHolder = part;
		else if (!partNULLState && !partEPSState)
			expressionHolder += " v " + part;
	}

	void unite(Expression part) {
		this->unite(part.getExpression());
	}
	Expression() {
		expressionHolder = "NULL";
	}

	Expression(string part) {
		expressionHolder = part;
	}

	~Expression() {

	}
};

map <int, vector<pair<int, string>>> MealyMachine;
int startState;
string inputLanguage;

void readMachine(map <int, vector<pair<int, string>>> & localMealyMachine, int & startState, string & inputLanguage, string inputFile) {
	ifstream fileStreamer(inputFile);
	fileStreamer >> startState >> inputLanguage;
	while (fileStreamer) {
		if( fileStreamer.eof() ) break;
		int keyState, nextState;
		string transition, outputSignal;
		fileStreamer >> keyState >> nextState >> transition >> outputSignal;
		localMealyMachine[keyState].push_back(make_pair(nextState, transition+outputSignal));
	}
}


void showMachine(map <int, vector<pair<int, string>>> localMealyMachine) {
	for (auto state : localMealyMachine) {
		for (auto vectorPart : state.second) 
			cout << state.first << " " << vectorPart.first << " " << vectorPart.second << endl;
	}
}

void deleteDeadEnds(map <int, vector<pair<int, string>>> & localMealyMachine, int startState) {
	vector <int> deadEndLog;
	for (auto state : localMealyMachine) {
		bool isDeadEnd = true;

		if (state.first == startState) {
			isDeadEnd = false;
			continue;
		}

		for (auto transition : state.second) {
			if (state.first != transition.first) {
				isDeadEnd = false;
				break;
			}
		}

		if (isDeadEnd)
			deadEndLog.push_back(state.first);
	}

	for (auto checkState : deadEndLog) {
		localMealyMachine.erase(checkState);
		for (auto & state : localMealyMachine)
			for (auto transition = state.second.begin(); transition != state.second.end(); transition++)
				if (transition->first == checkState)
					transition = --state.second.erase(transition);
	}

	if (deadEndLog.size() != 0)
		deleteDeadEnds(localMealyMachine, startState);
}

string buildRegularExpression(map <int, vector<pair<int, string>>> localMealyMachine, int startState, string inputWord) {

	map<int, vector<string>> regularExpressionPrototype;
	vector <vector <Expression>> matrixA, prototypeOfMatrixA;
	vector <Expression> vectorB, prototypeOfVectorB;
	vector <int> iterationQueue;
	for (int i = 0; i < localMealyMachine.size(); i++) {
		vector <Expression> line;
		Expression ex("NULL");
		for (int j = 0; j < localMealyMachine.size(); j++) {
			line.push_back(ex);
		}
		matrixA.push_back(line);
		vectorB.push_back(ex);
		iterationQueue.push_back(i);
	}
	swap(iterationQueue[0], iterationQueue[startState-1]);
	vectorB[0].unite("EPS");
	
	for (auto state : localMealyMachine) {
		vector <string> transitionWord;
		for (auto transition : state.second) {
			matrixA[transition.first-1][state.first-1].unite({1, transition.second[0]});

			size_t found = inputWord.find(transition.second[1]);
			if (found != string::npos)
				transitionWord.push_back({1, transition.second[0]});
		}
		if (transitionWord.size() > 0) {
			regularExpressionPrototype[state.first] = transitionWord;
		}
	}

	string resultPrototype;
	for (auto wordPart : regularExpressionPrototype) {
		resultPrototype += "S" + to_string(wordPart.first) + "(";
		for (auto transition : wordPart.second)
			resultPrototype += transition + " v ";
		resultPrototype = resultPrototype.substr(0, resultPrototype.length()-3);
		resultPrototype += ") v ";
	}

	resultPrototype = resultPrototype.substr(0, resultPrototype.length()-3);
	string result = "";
	prototypeOfMatrixA = matrixA;
	prototypeOfVectorB = vectorB;
	vector <int> iterationQueuePrototype = iterationQueue;
	for (auto wordPart : regularExpressionPrototype) {
		swap(iterationQueue[wordPart.first-1], iterationQueue[iterationQueue.size()-1]);
		int n;
		while (!iterationQueue.empty()) {
			n = iterationQueue[0];
			
			iterationQueue.erase(iterationQueue.begin(), iterationQueue.begin()+1);
			if (matrixA[n][n].getExpression() != "NULL") {
				if (vectorB[n].getExpression() != "NULL") 
					vectorB[n].concat("{" + matrixA[n][n].getExpression() + "}");
				for (int j : iterationQueue) {
					if (matrixA[n][j].getExpression() != "NULL")
						matrixA[n][j].concat("{" + matrixA[n][n].getExpression() + "}");
				}
			}
			for (int i : iterationQueue) {
				Expression ex;
				if (matrixA[i][n].getExpression() != "NULL") {
					if (vectorB[n].getExpression() != "NULL") {
						ex = vectorB[n];
						ex.concat(matrixA[i][n]);
						vectorB[i].unite(ex);
					}
					for (int j : iterationQueue) {
						if (matrixA[n][j].getExpression() != "NULL") {
							ex = matrixA[n][j];
							ex.concat(matrixA[i][n]);
							matrixA[i][j].unite(ex);
						}
					}
				}
			}
		}

		result += vectorB[wordPart.first-1].getExpression() + "(";
		matrixA = prototypeOfMatrixA;
		vectorB = prototypeOfVectorB;
		iterationQueue = iterationQueuePrototype;
		for (auto transition : wordPart.second)
			result += transition + " v ";
		result = result.substr(0, result.length()-3);
		result += ") v ";
	}
	result = result.substr(0, result.length()-3);
	return (resultPrototype + "\n" + result);
}

int main() {
	readMachine(MealyMachine, startState, inputLanguage, "input.txt");
	string regularExpression = buildRegularExpression(MealyMachine, startState, inputLanguage);
	if (regularExpression == "\n")
		cout << "\nNo propper state with output signals in input alphabet.\n\n";
	else
		cout << endl << regularExpression << endl;
	//string s = buildRegularExpression(MealyMachine, startState, inputLanguage);
	return 0;
}