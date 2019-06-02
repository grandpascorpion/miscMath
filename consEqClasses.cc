#include <vector>
#include <iostream>
#include <set>
#include <unordered_set>
#include <map>
#include <ctime>
#include <fstream>
#include "sys/time.h"

const bool DEBUG = false; 
const bool DEEP_DIVE = true;
using namespace std; using std::string; using std::cout; using std::cin; using std::vector; using std::set; using std::pair;
using std::unordered_set; 

typedef long UL;
typedef vector<pair<vector<UL>, pair<bool,bool>>> SubClassTupV; 
typedef map<vector<UL>, SubClassTupV> SubClassMap; 
typedef pair<vector<UL>, SubClassTupV> SubClassPair; // This would be a factor footprint plus a list of rows
typedef vector<vector<SubClassPair>> SubClassVec; 

// https://stackoverflow.com/questions/29855908/c-unordered-set-of-vectors
struct VectorHash {
  size_t operator()(const std::vector<UL>& v) const {
    std::hash<UL> hasher;
    size_t seed = 0;
    for (int i : v) {
      seed ^= hasher(i) + 0x9e3779b9 + (seed<<6) + (seed>>2);
    }
    return seed;
  }
};

typedef unordered_set<vector<UL>, VectorHash> SubClassSet;
//typedef set<vector<UL>> SubClassSet;

/*
Enhancements use powers instead of the raw numbers.  
Instead of 1 3 1 => 0 1 0 at level 3
Then, we have a smaller unique set of values.
For instance, 20 maps to 17496 = 6 * 4 * 3^6 (up to prime 19)
Then, a vector could be represented as a big integer with a max of 17496^20 which would fit into a 320-bit integer.
This would be a quarter of the memory of the vector in the set but a little more work computing the number.

Would it make sense to allow for the next higher power.

Other steps, combining layers of primes.

What about using an unordered set?  30% performance boost.

That might be nice with the big integer

The other things to do is to determine the savings collapses for each prime at each level.
and whether or not it makes sense to do that.  I think it usually would.

If only one entry in the chain.  It would have to be symmetric and you seemingly wouldn't have to multiply by it.
If you have only one entry in the factor field like 1 1 27 1 1.  Do you actually have to multiply by it?
(after the first level)
If there was only one, it would have to be symmetric, right?
Or should you strip out the symmetric entries and just multiply them first?
But this is kind of a fringe case.

*/

string timestamp()
{
  char buffer[50];

  time_t ltime;
  struct tm *Tm;
  ltime=time(NULL);
  Tm=localtime(&ltime);
  struct timeval detail_time;
  gettimeofday(&detail_time,NULL);
  sprintf(buffer, "%02d:%02d:%02d:%06d", Tm->tm_hour, Tm->tm_min, Tm->tm_sec, detail_time.tv_usec);  /* microseconds */
  string buffAsStr = buffer;
  return (buffAsStr);
}

bool isSymmetric(const vector<UL> &v) {
  auto vs = v.size();
  for (int i = 0; i < vs / 2; i++) if (v[i] != v[vs-i-1]) return false;
  return true; 
}

bool isFlip(const vector<UL> &v1, const vector<UL> &v2) { // 1 1 3 is a "flip" or mirror image of "3 1 1"
  auto v1s = v1.size();
  if (v1s != v2.size()) {
    cout << "Error: the sizes didn't match!" << endl; 
    exit(-1); 
  }
  auto it1 = v1.begin(); 
  auto it2 = v2.rbegin(); 
  for (; it1 != v1.end() && it2 != v2.rend(); it1++, it2++) if (*it1 != *it2) return false; 
  return true; 
}
 
SubClassMap genSubclass(int p, int n) {
  SubClassMap subclasses; 
  // determine the max prime
  int maxPower = p; 
  int tmp = (n-1)/p; 
  while (tmp > 0) maxPower *= p, tmp /= p;
  SubClassSet sv; 
  vector<UL> range(n, 0); 
  if (DEBUG) cout << "For n = " << n << ", p = " << p << " has maxPower = " << maxPower << endl; 
  for (int i = 0; i < maxPower; i++) {
    for (int j = i; j < i + n; j++) {
      int m = j % maxPower; 
      int pp; 
      if (m == 0) {
        pp = maxPower; 
      } else {
        pp = 1; 
        tmp = m; 
        while (!(tmp % p)) tmp /= p, pp *= p; 
      }
      range[j-i] = pp;   
    }
    if (sv.find(range) != sv.end()) continue; // already seen
    sv.insert(range); 
    // possible enhancement for later: collapse the "extra power" entries and increment the count

    vector<UL> ff; // we group by factor footprint
    for (auto pp: range) if (pp > 1) ff.push_back(pp);  
    sort(ff.begin(), ff.end());
    
    auto it = subclasses.find(ff); 
    auto symFlag = isSymmetric(range); 
    bool flipFlag = false;  
    if (it == subclasses.end()) {
      subclasses[ff].push_back(make_pair(range, make_pair(flipFlag, symFlag)));  
    } else {
      for (auto &v : it->second) {
        if (isFlip(v.first, range)) {
          flipFlag = true; 
          break; 
        }
      } 
      // only push the uniq entries if p = 2 (because that's the first prime)
      if (p !=2 || !flipFlag) it->second.push_back(make_pair(range, make_pair(flipFlag, symFlag))); 
    }
    if (DEBUG) {
      cout << "\tAt index " << i << ", we have: "; for (auto p2 : range) cout << p2 << " "; cout << endl; 
    }
  }
  if (DEBUG) cout << endl;  
  if (!subclasses.size()) {
    cout << "Subclasses was blank!" << endl;
    exit(1); 
  }
  if (DEBUG) {
    for (auto &pr : subclasses) {
      cout << "Processing ff = "; for (auto &pp : pr.first) cout << pp << " "; cout << ": " << endl;
      for (auto &v : pr.second) {
        cout << "\t"; for (auto &pp : v.first) cout << pp << " "; 
        cout << "(Flip? " << v.second.first << ", Sym? " << v.second.second << ")" << endl;
      }
    }
  }
  return (subclasses);
}

UL processSubClass(SubClassSet &scSet, const SubClassVec &scVec, const vector<int> &indexes, const vector<UL> &wv, int lvl, bool sym, int primeLenMatch, UL &missCt) {
  UL ct = 0; 
  if (DEBUG) cout << "Processing lvl = " << lvl << " and " << indexes[lvl] << endl; 
  for (auto &pr : scVec[lvl][indexes[lvl]].second) { // correspond set of rows for a given factor footprint
    if (sym && pr.second.first) continue; // we are symmetric but encountered a flipped entry ... Skip!
    bool newSym = sym && pr.second.second; // check if still symmetric
    if (DEBUG) {cout << endl << "____ " << indexes[lvl]; for (int b = 0; b <= lvl; b++) cout << "\t"; for (auto pp : pr.first) cout << pp << " "; cout << endl << endl; }
    auto newWV(pr.first); 
    if (lvl > 0) for (int i = 0; i < wv.size(); i++) newWV[i] *= wv[i]; // multiply each entry by the old wv
    if (DEBUG) { cout << "\tProcessing wv = "; for (auto v : newWV) cout << v << " "; cout << endl; }
    auto newLvl = lvl + 1;  
    if (newLvl == scVec.size()) { // we have reached the end. we can't go any further
      sort(newWV.begin(), newWV.end()); // it's ok to sort this because we are at the end
      // check to see if this exists
      if (scSet.find(newWV) == scSet.end()) {
        scSet.insert(newWV); 
        if (primeLenMatch) { // count the number of distinct values
          int lastVal = 0; 
          int lastCt = 0; 
          for (auto v: newWV) { // insert one for each distinct 
            if (lastVal != v) lastCt++; 
            lastVal = v; 
          }
          if (DEBUG) { cout << "Added " << lastCt << " at end: wv = "; for (auto v : newWV) cout << v << " "; cout << endl; }
          ct += lastCt;  
        } else {
          if (DEBUG) { cout << "Added: wv = "; for (auto v : newWV) cout << v << " "; cout << endl; }          
          ct++; 
        }
      } else {
        missCt++; 
      } 
    } else {
      ct += processSubClass(scSet, scVec, indexes, newWV, newLvl, newSym, primeLenMatch, missCt); 
    }
  }
  return ct; 
}

void backupFile (string fName) {
  string backup = fName + "." + timestamp(); 

  cout << "Backing up: " << fName << " to " << backup << endl; 
  ifstream source(fName); 
  ofstream dest(backup); 

  istreambuf_iterator<char> begin_source(source);
  istreambuf_iterator<char> end_source;
  ostreambuf_iterator<char> begin_dest(dest);
  copy(begin_source, end_source, begin_dest);
  source.close();
  dest.close();
}

int main(int argc, const char *argv[])
{
  // list of primes
  vector<int> primes{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97};
  const int UB = 100; // must be in sync with primes above
  int sv = 3;
  if (argc > 1) sv = atoi(argv[1]);
  if (sv > UB) {
    cout << "The search param n must be <= " << UB << endl; 
    exit(1); 
  }
  ofstream subCountFile;
  if (DEEP_DIVE) {
    string fName = "consSubCounts.txt";
    backupFile(fName); 
    subCountFile.open(fName); // restart it
  } 

  SubClassSet scSet;
  if (DEEP_DIVE) scSet.reserve(10000000); // revisit when going beyond 20

  cout << "Running from n = " << sv << " to " << UB << endl;
  for (int n = sv; n <= UB; n++) {
    // cycle through the primes
    int primeLenMatch = 0;
    SubClassVec scVec; 
    for (auto p: primes) {
      if (p > n) continue;
      if (p == n) {
        // add an optimization when n is prime: to add each in by the number of distinct values
        
        // what about when you have an entry that has all unique values
        // then you can multiply it by anything and it will still be unique
        // how do you know there is only one combination though
        primeLenMatch = p;
        break;
      }
      auto subClass = genSubclass(p,n); 
      vector<SubClassPair> vscp;       
      for (auto &pr : subClass) vscp.push_back(pr); 
      scVec.push_back(vscp);
    }
    // After you compile the list, cycle through them, one subset at a time 
    // Find a "product" of all the subproblems and then compute them one at a time so unique sets aren't too big 
    UL prod = 1; 
    for (auto &ff : scVec) prod *= ff.size();

    cout << "Here is prod = " << prod << " at n = " << n << endl; 

    vector<int> index; 
    vector<UL> dummy; // empty vector to get things started
    UL totalCt = 0; 
    for (UL x = 0; x < prod; x++) { // now we iterate through all of the combinations
      // we must iterate through the primes in the list.  If it's on a prime, then there's a final step
      // of counting all of the combinations (based on unique values). 
      // you also have to keep track of which items are symmetric going in.
      vector<int> indexes;
      auto tmp = x; 
      for (int y = 0; y < scVec.size(); y++) {
        auto s = scVec[y].size(); 
        indexes.push_back(tmp % s);
        if (DEBUG) cout << "For x = " << x << ", we have " << tmp %s << " for " << s << " at index = " << y << endl;  
        tmp /= s; 
      }
      // now we have a set of indices we can pass in and iterate through
      if (DEEP_DIVE) {
        scSet.clear();
        UL missCt = 0; 
        UL subCt = processSubClass(scSet, scVec, indexes, dummy, 0, true, primeLenMatch, missCt);  // XXX pass in the prime flag.  Make the primes global?
        if (DEBUG) cout << "\tThe subcount for x = " << x << " of " << prod -1 << " was " << subCt << " vs. " << scSet.size() 
                        << ".  There were " << missCt << " misses.  (at " << timestamp() << ")" << endl; 
        subCountFile << n << " " << x << " " << scSet.size() << endl;   
        totalCt += subCt; 
      }
    }
    if (DEEP_DIVE) { cout << "The total equiv class count for n = " << n << " was: " << totalCt << ". (" << timestamp() << ")" << endl;
     subCountFile << n << " TOTAL " << totalCt << endl; 
    }
  }
  if (DEEP_DIVE) subCountFile.close(); 
}

