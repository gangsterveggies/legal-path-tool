#include <stdio.h>
#include <assert.h>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <string>

using namespace std;

#define MXTERM 1000
#define MXITER 11
#define MXLABEL 50
#define MXLEVEL 20
#define MXSTEPS 6

#define TYPE_PRINT 0
#define TYPE_LINEAR 1
#define TYPE_TERM 2
#define TYPE_REDUCE 3
#define TYPE_WEAK 4
#define TYPE_METRIC 5

int subs = 0;

struct Node
{
  bool isLambda;
  bool isVar;
  string var, label;
  Node *abt, *arg, *par;
};

struct Path
{
  vector<string> path;

  void push_back(string s)
    {
      path.push_back(s);
    }

  string front()
    {
      return path.front();
    }

  string back()
    {
      return path.back();
    }

  const char* c_str()
    {
      string fin = "";

      for (auto s : path)
        fin += s;

      return fin.c_str();
    }

  Path operator+ (Path p)
    {
      vector<string> pathr;

      pathr = path;
      for (string s : p.path)
        pathr.push_back(s);

      return {pathr};
    }

  bool operator== (Path p)
    {
      if (path.size() != p.path.size())
        return false;

      for (int i = 0; i < int(path.size()); i++)
        if (path[i] != p.path[i])
          return false;
      return true;
    }

  bool operator!= (Path p)
    {
      if (path.size() != p.path.size())
        return true;

      for (int i = 0; i < int(path.size()); i++)
        if (path[i] != p.path[i])
          return true;
      return false;
    }

  bool operator< (const Path b) const
    {
      for (int i = 0; i < int(path.size()) && i < int(b.path.size()); i++)
        if (path[i] != b.path[i])
          return path[i] < b.path[i];
      return path.size() < b.path.size();
    }
};

struct PathMetric
{
  int s, n;
  vector<int> mset;

  const char* c_str()
    {
      string fin = "<";
      fin += to_string(s);
      fin += ",";
      fin += to_string(n);
      fin += ",{";

      bool fs = true;
      for (int i : mset)
      {
        if (!fs)
          fin += ",";
        fs = false;
        fin += to_string(i);
      }

      fin += "}>";

      return fin.c_str();
    }

  bool operator< (const PathMetric b) const
    {
      if (s != b.s)
        return s > b.s;
      if (n != b.n)
        return n > b.n;
      for (int i = 0; i < int(mset.size()) && i < int(b.mset.size()); i++)
        if (mset[i] != b.mset[i])
          return mset[i] > b.mset[i];
      return mset.size() > b.mset.size();
    }

  bool cmp(PathMetric b)
    {
      if (s != b.s)
        return s < b.s;
      if (n != b.n)
        return n < b.n;
      for (int i = 0; i < int(mset.size()) && i < int(b.mset.size()); i++)
        if (mset[i] != b.mset[i])
          return mset[i] < b.mset[i];
      return mset.size() < b.mset.size();
    }
};

char input[MXTERM];
map<string, Node*> labelNode;
map<string, char> varMap;
vector<Path> atPaths, lbPaths, vrPaths;
vector<Path> atNew, lbNew, vrNew;
vector<Path> atPrev, lbPrev, vrPrev;
vector<Path> S[MXLEVEL];
int pos, execType, weakLevel;
bool verbose = false;

Node* mknode()
{
  Node* n = new Node();
  n->isLambda = false;
  n->isVar = false;
  n->label = "a";
  return n;
}

void serror(const char* msg)
{
  fprintf(stderr, "Error on col %d: %s\n", pos + 1, msg);
  exit(1);
}

bool nVar(Node* nd)
{
  return nd->isVar;
}

bool nLambda(Node* nd)
{
  return nd->isLambda;
}

bool nApp(Node* nd)
{
  return !nd->isLambda && !nd->isVar;
}

bool isVar(char s)
{
  return ((s >= 'a') && (s <= 'z')) ||
    ((s >= '0') && (s <= '9'));
}

string itoa(int a)
{
  string s = "";

  while (a)
  {
    s += (a % 10) + '0';
    a /= 10;
  }

  reverse(s.begin(), s.end());

  return s;
}

Path reverse(Path s)
{
  vector<string> ns = s.path;
  reverse(ns.begin(), ns.end());
  return {ns};
}

string nextLabel(string s)
{
  if (s[0] == 'z')
  {
    s[0] = 'a';
    s += '\'';
  }
  else
    s[0]++;
  return s;
}

bool curChar(char val)
{
  return val == input[pos];
}

char curChar()
{
  return input[pos];
}

char nextChar()
{
  char s = curChar();
  pos++;
  return s;
}

void rewire(Node* &root, Node* &cur, Node* r)
{
  if (root == NULL)
  {
    root = r;
    cur = r;
  }
  else
  {
    Node* tmp = mknode();
    tmp->abt = cur;
    tmp->arg = r;

    if (cur != NULL)
    {
      tmp->par = cur->par;
      cur->par = tmp;
    }

    if (tmp->arg != NULL)
      tmp->arg->par = tmp;

    if (cur == root)
      root = tmp;

    cur = tmp;
  }
}

Node* parseTerm()
{
  Node *root = NULL, *cur;

  while (1)
  {
    char s = nextChar();

    if (s == '\\')
    {
      Node* r = mknode(), *c;
      
      vector<string> varList;
      s = nextChar();
      string vr = string(1, s);
      while (isVar(s))
      {
        s = nextChar();
        if (s >= 'a' && s <= 'z')
        {
          varList.push_back(vr);
          vr = string(1, s);
        }
        else if (s >= '0' && s <= '9')
          vr += s;
      }
      if (!vr.empty())
          varList.push_back(vr);

      if (s != '.')
        serror("invalid lambda variable end character");

      if (varList.empty())
        serror("invalid variables for lambda");

      r->isLambda = true;
      r->var = varList[0];
      c = r;

      for (int i = 1; i < int(varList.size()); i++)
      {
        Node* tmp = mknode();
        tmp->isLambda = true;
        tmp->var = varList[i];
        tmp->par = c;
        c->abt = tmp;
        c = tmp;
      }

      s = nextChar();
      if (s != '(')
        serror("lambda arguments must be enclosed in parenthesis");

      c->abt = parseTerm();
      if (c->abt == NULL)
        serror("invalid lambda content");
      c->abt->par = c;

      s = nextChar();
      if (s != ')')
        serror("invalid syntax, expecting )");

      rewire(root, cur, r);
    }
    else if (isVar(s))
    {
      Node* r = mknode();
      r->isVar = true;
      r->var = string(1, s);

      rewire(root, cur, r);
    }
    else if (s == '(')
    {
      Node* r = parseTerm();
      if (r == NULL)
        serror("invalid parenthesis expression");

      rewire(root, cur, r);

      if (!curChar(')'))
        serror("invalid syntax, expecting )");
      nextChar();
    }
    else if (s == ')' || s == '\0')
    {
      pos--;
      break;
    }
    else
      serror("invalid character");
  }

  return root;
}

void printTerm(Node* cur, int pLabel = 0)
{
  if (cur == NULL)
    return;

  if (cur->isVar)
  {
    if (pLabel)
      printf("(");
    printf("%s", cur->var.c_str());
    if (pLabel)
      printf("^%s)", cur->label.c_str());
  }
  else if (cur->isLambda)
  {
    printf("\\%s.", cur->var.c_str());

    if (!nApp(cur->abt))
      printf("(");

    printTerm(cur->abt, pLabel);

    if (!nApp(cur->abt))
      printf(")");

    if (pLabel)
      printf("^%s", cur->label.c_str());
  }
  else
  {
    printf("(");

    if (nLambda(cur->abt))
      printf("(");
    printTerm(cur->abt, pLabel);
    if (nLambda(cur->abt))
      printf(")");

    if (nLambda(cur->arg))
      printf("(");
    printTerm(cur->arg, pLabel);
    if (nLambda(cur->arg))
      printf(")");

    printf(")");
    if (pLabel)
      printf("^%s", cur->label.c_str());
  }
}

string labelTerm(Node* cur, string label)
{
  if (cur == NULL)
    return label;

  labelNode[label] = cur;

  if (cur->isVar)
  {
    cur->label = label;
    return nextLabel(label);
  }
  else if (cur->isLambda)
  {
    cur->label = label;
    return labelTerm(cur->abt, nextLabel(label));
  }
  else
  {
    cur->label = label;
    string tmp = labelTerm(cur->abt, nextLabel(label));
    return labelTerm(cur->arg, tmp);
  }
}

char varTerm(Node* cur, char label)
{
  if (cur == NULL)
    return label;

  if (cur->isVar)
  {
    if (varMap.count(cur->var) == 0)
      varMap[cur->var] = label++;
    cur->var = string(1, varMap[cur->var]);

    return label;
  }
  else if (cur->isLambda)
  {
    char prev = '0';

    if (varMap.count(cur->var) != 0)
      prev = varMap[cur->var];

    varMap[cur->var] = label++;

    cur->var = string(1, varMap[cur->var]);

    char ls = varTerm(cur->abt, label);

    if (prev != '0')
      varMap[cur->var] = prev;
    else if (varMap.count(cur->var) != 0)
      varMap.erase(varMap.find(cur->var));

    return ls;
  }
  else
  {
    char tmp = varTerm(cur->abt, label);
    return varTerm(cur->arg, tmp);
  }
}

void checkPar(Node* term, Node* p)
{
  if (term == NULL)
    return;

  assert(term->par == p);

  if (nApp(term))
  {
    checkPar(term->abt, term);
    checkPar(term->arg, term);
  }
  else if (nLambda(term))
    checkPar(term->abt, term);
}

void addPath(Path path)
{
  Node* base = labelNode[path.back()];

  if (nVar(base))
  {
    if (find(vrNew.begin(), vrNew.end(), path) == vrNew.end() &&
        find(vrPaths.begin(), vrPaths.end(), path) == vrPaths.end() &&
        find(vrPrev.begin(), vrPrev.end(), path) == vrPrev.end())
      vrNew.push_back(path);
  }
  else if (nLambda(base))
  {
    if (find(lbNew.begin(), lbNew.end(), path) == lbNew.end() &&
        find(lbPaths.begin(), lbPaths.end(), path) == lbPaths.end() &&
        find(lbPrev.begin(), lbPrev.end(), path) == lbPrev.end())
      lbNew.push_back(path);
  }
  else if (nApp(base))
  {
    if (find(atNew.begin(), atNew.end(), path) == atNew.end() &&
        find(atPaths.begin(), atPaths.end(), path) == atPaths.end() &&
        find(atPrev.begin(), atPrev.end(), path) == atPrev.end())
      atNew.push_back(path);
  }
}

void initialPaths(Node* cur)
{
  if (cur == NULL)
    return;

  if (cur->isVar)
    return;
  else if (cur->isLambda)
    initialPaths(cur->abt);
  else
  {
    Node* base = cur->abt;

    Path path;
    path.push_back(base->label);

    addPath(path);

    initialPaths(cur->abt);
    initialPaths(cur->arg);
  }  
}

void lambdaCompose(Path lpath, Path vpath)
{
  Node* lnode = labelNode[lpath.back()];
  Node* vnode = labelNode[vpath.back()];

  if (lnode->var != vnode->var)
    return;

  if (execType == TYPE_PRINT)
    printf("\\ composing %s with %s\n", lpath.c_str(), vpath.c_str());

  Path result;
  result.push_back(labelNode[lpath.front()]->par->arg->label);

  Path npath = vpath + reverse(lpath) + result;
  addPath(npath);
}

void atCompose(Path lpath, Path apath)
{
  Node* lnode = labelNode[lpath.back()];
  Node* lnode2 = labelNode[lpath.front()];
  Node* anode = labelNode[apath.back()];

  if (lnode2->par != anode)
    return;

  if (execType == TYPE_PRINT)
    printf("@ composing %s with %s\n", lpath.c_str(), apath.c_str());

  Path result;
  result.push_back(lnode->abt->label);

  Path npath = apath + lpath + result;
  addPath(npath);
}

void lambdaComposeFromList(vector<Path>& llist, vector<Path>& vlist)
{
  for (auto lpath : llist)
    for (auto vpath : vlist)
      lambdaCompose(lpath, vpath);
}

void atComposeFromList(vector<Path>& llist, vector<Path>& alist)
{
  for (auto lpath : llist)
    for (auto apath : alist)
      atCompose(lpath, apath);
}

void copyPaths(int slevel)
{
  for (auto path : lbPrev)
    S[slevel - 1].push_back(path);
}

void printPaths(int slevel)
{
  if (slevel > 0)
    printf("Level %d:\n", slevel);

  printf("@-paths:\n");
  if (slevel == 0)
    for (auto path : atPaths)
      printf("%s\n", path.c_str());
  for (auto path : atPrev)
    printf("%s\n", path.c_str());

  printf("\n\\-paths:\n");
  if (slevel == 0)
    for (auto path : lbPaths)
      printf("%s\n", path.c_str());
  for (auto path : lbPrev)
    printf("%s\n", path.c_str());

  copyPaths(slevel);

  printf("\nv-paths:\n");
  if (slevel == 0)
    for (auto path : vrPaths)
      printf("%s\n", path.c_str());
  for (auto path : vrPrev)
    printf("%s\n", path.c_str());
}

int fillPaths(Node* term)
{
  atPaths.clear(), lbPaths.clear(), vrPaths.clear();
  atNew.clear(), lbNew.clear(), vrNew.clear();
  atPrev.clear(), lbPrev.clear(), vrPrev.clear();

  initialPaths(term);

  for (int i = 0; i < MXITER; i++)
    atComposeFromList(lbNew, atNew);

  int changes = !atNew.empty() || !lbNew.empty() || !vrNew.empty();

  for (auto path : atNew)
    atPrev.push_back(path);

  for (auto path : lbNew)
    lbPrev.push_back(path);

  for (auto path : vrNew)
    vrPrev.push_back(path);
  atNew.clear(), lbNew.clear(), vrNew.clear();

  int iter = 1;
  for (; iter < MXITER && changes; )
  {
    S[iter - 1].clear();

    if (execType == TYPE_PRINT)
    {
      printPaths(iter++);
      printf("\n");
    }
    else
      copyPaths(iter++);

    lambdaComposeFromList(lbPrev, vrPrev);
    lambdaComposeFromList(lbPaths, vrPrev);
    lambdaComposeFromList(lbPrev, vrPaths);

    for (auto path : atPrev)
      atPaths.push_back(path);

    for (auto path : lbPrev)
      lbPaths.push_back(path);

    for (auto path : vrPrev)
      vrPaths.push_back(path);
    atPrev.clear(), lbPrev.clear(), vrPrev.clear();

    for (auto path : atNew)
      atPrev.push_back(path);

    for (auto path : lbNew)
      lbPrev.push_back(path);

    for (auto path : vrNew)
      vrPrev.push_back(path);

    changes = !atNew.empty() || !lbNew.empty() || !vrNew.empty();
    atNew.clear(), lbNew.clear(), vrNew.clear();

    int atchanges = 1;
    while (atchanges)
    {
      atComposeFromList(lbPrev, atPrev);
      atComposeFromList(lbPaths, atPrev);
      atComposeFromList(lbPrev, atPaths);

      for (auto path : atNew)
        atPrev.push_back(path);

      for (auto path : lbNew)
        lbPrev.push_back(path);

      for (auto path : vrNew)
        vrPrev.push_back(path);

      atchanges = !atNew.empty() || !lbNew.empty() || !vrNew.empty();
      atNew.clear(), lbNew.clear(), vrNew.clear();
    }

    for (auto path : atNew)
      atPrev.push_back(path);

    for (auto path : lbNew)
      lbPrev.push_back(path);

    for (auto path : vrNew)
      vrPrev.push_back(path);

    changes = changes || !atNew.empty() || !lbNew.empty() || !vrNew.empty();

    atNew.clear(), lbNew.clear(), vrNew.clear();
  }

  return iter - 1;
}

int varCount(Node* cur, string var)
{
  if (cur == NULL)
    return 0;

  if (nApp(cur))
    return varCount(cur->abt, var) + varCount(cur->arg, var);

  if (nLambda(cur) && cur->var != var)
    return varCount(cur->abt, var);

  if (nVar(cur))
    return (cur->var == var);
}

bool notLinear(Path p)
{
  Node* n = labelNode[p.back()];
  return varCount(n->abt, n->var) > 1;
}

Node* copyTerm(Node* org, Node* dst, Node* prev)
{
  if (org == NULL)
    return NULL;

  dst->par = prev;

  if (nApp(org))
  {
    dst->abt = copyTerm(org->abt, mknode(), dst);
    dst->arg = copyTerm(org->arg, mknode(), dst);
  }
  else if (nLambda(org))
  {
    dst->isLambda = true;
    dst->var = org->var;
    dst->abt = copyTerm(org->abt, mknode(), dst);
  }
  else
  {
    dst->isVar = true;
    dst->var = org->var;
  }

  return dst;
}

void replace_n(Node* term, string lb, int n)
{
  if (term == NULL)
    return;

  if (term->label == lb)
  {
    Node* pterm = term->par;
    Node* qterm = pterm->abt;
    Node* nterm = pterm->arg;
    Node* cr = pterm;

    for (int i = 1; i < n; i++)
    {
      cr->abt = mknode();
      cr->arg = copyTerm(nterm, mknode(), cr);
      cr->abt->par = cr;
      cr->arg->par = cr;
      cr = cr->abt;
    }

    cr->abt = qterm;
    cr->arg = nterm;
    cr->abt->par = cr;
    cr->arg->par = cr;
  }
  else
  {
    if (nApp(term))
    {
      replace_n(term->abt, lb, n);
      replace_n(term->arg, lb, n);
    }
    else if (nLambda(term))
      replace_n(term->abt, lb, n);
  }
}

int cleanup(Node* term, string var, int cr)
{
  if (term == NULL)
    return cr;

  if (nApp(term))
  {
    int crl = cleanup(term->abt, var, cr);
    return cleanup(term->arg, var, crl);
  }
  else if (nLambda(term) && term->var != var)
    return cleanup(term->abt, var, cr);
  else
  {
    if (term->var == var)
    {
      term->var += itoa(cr);
      cr++;
    }

    return cr;
  }
}

void replace(Node* term, string lb, int n)
{
  if (term == NULL)
    return;

  if (term->label == lb)
  {
    assert(nLambda(term));

    Node* cr = term;
    Node* fn = term->abt;
    string base = term->var;

    for (int i = 1; i <= n; i++)
    {
      cr->var = base;
      cr->var += itoa(i);

      if (i != n)
      {
        cr->abt = mknode();
        cr->abt->isLambda = true;
        cr->abt->par = cr;
        cr = cr->abt;
      }
    }

    cleanup(fn, base, 1);
    cr->abt = fn;
    cr->abt->par = cr;
  }
  else
  {
    if (nApp(term))
    {
      replace(term->abt, lb, n);
      replace(term->arg, lb, n);
    }
    else if (nLambda(term))
      replace(term->abt, lb, n);
  }
}

void linearize(Path p, Node* term)
{
  Node* n = labelNode[p.back()];
  int num = varCount(n->abt, n->var);

  replace(term, p.back(), num);
  replace_n(term, p.front(), num);

  if (verbose)
  {
    printf("%s: (%s, %s) - ", p.c_str(), p.back().c_str(), p.front().c_str());
    printf("%d of %s", num, n->var.c_str());
    printf(" not");
    printf(" linear\n");
  }
}

Node* substitute(Node* term, Node* sb, string var)
{
  if (term == NULL)
    return NULL;

  if (nApp(term))
  {
    term->abt = substitute(term->abt, sb, var);
    term->arg = substitute(term->arg, sb, var);

    term->abt->par = term;
    term->arg->par = term;

    return term;
  }
  else if (nLambda(term) && term->var != var)
  {
    term->abt = substitute(term->abt, sb, var);
    term->abt->par = term;
    return term;
  }
  else if (term->var != var)
    return term;
  else
  {
    subs++;
    weakLevel++;
    return copyTerm(sb, mknode(), term->par);
  }
}

void betaReduce(Node* term)
{
  term->abt->abt = substitute(term->abt->abt, term->arg, term->abt->var);

  Node* abt = term->abt->abt;
  term->var = abt->var;
  term->isLambda = abt->isLambda;
  term->isVar = abt->isVar;
  term->abt = abt->abt;
  term->abt->par = term;
  term->arg = abt->arg;
  if (term->arg != NULL)
    term->arg->par = term;
}

Node* getRedex(Node* term)
{
  if (term == NULL)
    return NULL;

  if (nApp(term))
  {
    if (nLambda(term->abt))
      return term;

    Node* a = getRedex(term->abt);
    if (a != NULL)
      return a;
    return getRedex(term->arg);
  }
  else if (nLambda(term))
    return getRedex(term->abt);

  return NULL;
}

Node* normalize(Node* term, bool &isWeak, int verbose = 0)
{
  Node* fin = copyTerm(term, mknode(), NULL);

  varMap.clear();
  varTerm(fin, 'a');

  Node* redux = getRedex(fin);
  int mx = 0;

  while (redux != NULL)
  {
    weakLevel = 0;
    betaReduce(redux);
    mx = max(mx, weakLevel);

    redux = getRedex(fin);

    if (verbose)
    {
      printTerm(fin);
      printf("\n");
    }
  }

  isWeak = mx <= 1;

  return fin;
}

int countTot(Node* term, string var)
{
  if (term == NULL)
    return 0;

  if (nApp(term))
    return countTot(term->abt, var) + countTot(term->arg, var);
  else if (nLambda(term))
  {
    if (term->var != var)
      return countTot(term->abt, var);
    return 0;
  }
  else
    return term->var == var;
}

void countFree(Node* term, multiset<string>& freeSet, map<string, int>& ctMap)
{
  if (term == NULL)
    return;

  if (nApp(term))
  {
    countFree(term->abt, freeSet, ctMap);
    countFree(term->arg, freeSet, ctMap);
  }
  else if (nLambda(term))
  {
    auto it = freeSet.insert(term->var);
    countFree(term->abt, freeSet, ctMap);
    freeSet.erase(it);
  }
  else
  {
    if (freeSet.find(term->var) == freeSet.end())
      ctMap[term->var]++;
  }
}

int pathInside(Node* term, string var)
{
  if (term == NULL)
    return 0;

  if (term->label == var)
    return 1;

  if (nApp(term))
    return (pathInside(term->abt, var) + pathInside(term->arg, var)) > 0;
  else if (nLambda(term))
    return pathInside(term->abt, var);
  else
    return 0;
}

PathMetric calcMetric(Path p, Node* term, int s)
{
  PathMetric pm;

  Node* st = labelNode[p.back()];
  Node* ed = labelNode[p.front()]->par->arg;

  int n = max(1, countTot(st->abt, st->var));

  multiset<string> freeSet;
  map<string, int> ctMap;
  countFree(ed, freeSet, ctMap);

  vector<int> mset;
  for (auto pt : ctMap)
    mset.push_back(pt.second);
  sort(mset.begin(), mset.end());
  reverse(mset.begin(), mset.end());

  pm.s = s;
  pm.n = n;
  pm.mset = mset;

  return pm;
}

vector<pair<PathMetric, Path> > fillMetricList(int iter, Node* term)
{
  vector<pair<PathMetric, Path> > metricList;
  for (int i = 0; i < iter; i++)
    for (auto path : S[i])
      metricList.push_back(make_pair(calcMetric(path, term, i), path));

  sort(metricList.begin(), metricList.end());

  return metricList;
}

int main(int argc, char** argv)
{
  execType = TYPE_PRINT;

  for (int i = 1; i < argc; i++)
  {
    if (argv[i][0] != '-')
      continue;

    if (argv[i][1] == 'p')
      execType = TYPE_PRINT;
    else if (argv[i][1] == 'l')
      execType = TYPE_LINEAR;
    else if (argv[i][1] == 't')
      execType = TYPE_TERM;
    else if (argv[i][1] == 'r')
      execType = TYPE_REDUCE;
    else if (argv[i][1] == 'w')
      execType = TYPE_WEAK;
    else if (argv[i][1] == 'm')
      execType = TYPE_METRIC;
    else if (argv[i][1] == 'v')
      verbose = true;
  }

  scanf(" %s", input);

  pos = 0;
  Node* term = parseTerm();
  if (term == NULL)
    serror("malformed expression");

  if (execType == TYPE_PRINT || execType == TYPE_TERM)
  {
    printTerm(term);
    printf("\n");
  }

  labelTerm(term, "a");

  if (execType == TYPE_PRINT || execType == TYPE_TERM)
  {
    printTerm(term, 1);
    printf("\n");
  }

  if (execType == TYPE_PRINT)
  {
    int iter = fillPaths(term);

    for (int i = 0; i < iter; i++)
    {
      printf("S%d: {", i + 1);

      for (auto path : S[i])
      {
        printf("%s", path.c_str());
        if (path != S[i].back())
          printf(",");
      }

      printf("}\n");
    }
  }
  else if (execType == TYPE_LINEAR)
  {
    vector<pair<PathMetric, Path> > pMetricList, cMetricList;
    bool linear = false;
    int iter;
    int steps = 0;

    while (!linear && steps < MXSTEPS)
    {
      steps++;
      linear = true;
      
      labelNode.clear();
      labelTerm(term, "a");
      iter = fillPaths(term);
      cMetricList = fillMetricList(iter, term);

      if (verbose)
        for (auto ele : cMetricList)
        {
          printf("%s :", ele.first.c_str());
          printf(" %s\n", ele.second.c_str());
        }

      for (int i = 0; i < iter; i++)
        for (auto path : S[i])
          if (notLinear(path))
          {
            linearize(path, term);

            varMap.clear();
            varTerm(term, 'a');

            printTerm(term, 0);
            printf("\n");

            checkPar(term, NULL);
            linear = false;
            goto reset;
          }

    reset:
      if (!pMetricList.empty())
      {
        bool fl = false;
        for (int i = 0; i < int(pMetricList.size()) && i < int(cMetricList.size()); i++)
        {
          if (pMetricList[i].first.cmp(cMetricList[i].first))
          {
            printf("Index: %d\n", i);
            fl = true;
            break;
          
          }

          if (cMetricList[i].first.cmp(pMetricList[i].first))
            break;
        }   

        if (fl)
          printf("Not smaller...\n");
      }

      pMetricList = cMetricList;
    }

    labelTerm(term, "a");
    varMap.clear();
    varTerm(term, 'a');

    if (verbose)
    {
      printTerm(term, 1);
      printf("\n");
    }

    if (verbose)
    {
      for (int i = 0; i < iter; i++)
      {
        printf("S%d: {", i + 1);
        
        for (auto path : S[i])
        {
          printf("%s", path.c_str());
          if (path != S[i].back())
            printf(",");
        }

        printf("}\n");
      }
    }
  }
  else if (execType == TYPE_REDUCE)
  {
    printTerm(term);
    printf("\n");

    bool tmp;
    Node* final = normalize(term, tmp, 1);

    printTerm(final);
    printf("\n");

    printf("Subs: %d\n", subs);
  }
  else if (execType == TYPE_WEAK)
  {
    bool isWeak;
    Node* final = normalize(term, isWeak, 1);

    printf("The term is %s linear\n", isWeak ? "weak" : "not weak");
  }
  else if (execType == TYPE_METRIC)
  {
    int iter = fillPaths(term);
    vector<pair<PathMetric, Path> > metricList = fillMetricList(iter, term);

    for (auto ele : metricList)
    {
      printf("%s :", ele.first.c_str());
      printf(" %s\n", ele.second.c_str());
    }
  }

  return 0;
}
