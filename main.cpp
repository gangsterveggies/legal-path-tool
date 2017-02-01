#include <stdio.h>
#include <assert.h>
#include <vector>
#include <map>
#include <algorithm>

using namespace std;

#define MXTERM 1000
#define MXITER 20
#define MXLABEL 50
#define MXLEVEL 20

#define TYPE_PRINT 0
#define TYPE_LINEAR 1
#define TYPE_TERM 2

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
};

char input[MXTERM];
map<string, Node*> labelNode;
vector<Path> atPaths, lbPaths, vrPaths;
vector<Path> atNew, lbNew, vrNew;
vector<Path> atPrev, lbPrev, vrPrev;
vector<Path> S[MXLEVEL];
int pos, execType;

Node* mknode()
{
  Node* n = new Node();
  n->isLambda = false;
  n->isVar = false;
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
  return (s >= 'a') && (s <= 'z');
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
      
      vector<char> varList;
      s = nextChar();
      while (isVar(s))
      {
        varList.push_back(s);
        s = nextChar();
      }

      if (s != '.')
        serror("invalid lambda variable end character");

      if (varList.empty())
        serror("invalid variables for lambda");

      r->isLambda = true;
      r->var = string(1, varList[0]);
      c = r;

      for (int i = 1; i < int(varList.size()); i++)
      {
        Node* tmp = mknode();
        tmp->isLambda = true;
        tmp->var = string(1, varList[i]);
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
    printf("(\\%s.", cur->var.c_str());
    printTerm(cur->abt, pLabel);
    printf(")");
    if (pLabel)
      printf("^%s", cur->label.c_str());
  }
  else
  {
    printf("(");
    printTerm(cur->abt, pLabel);
    printTerm(cur->arg, pLabel);
    printf(")");
    if (pLabel)
      printf("^%s", cur->label.c_str());
  }
}

char labelTerm(Node* cur, char label)
{
  if (cur == NULL)
    return label;

  string s = "";
  s += label;
  labelNode[s] = cur;

  if (cur->isVar)
  {
    cur->label = label++;
    return label;
  }
  else if (cur->isLambda)
  {
    cur->label = label++;
    return labelTerm(cur->abt, label);
  }
  else
  {
    cur->label = label++;
    char tmp = labelTerm(cur->abt, label);
    return labelTerm(cur->arg, tmp);
  }
}

void addPath(Path path)
{
  Node* base = labelNode[path.back()];

  if (nVar(base))
    vrNew.push_back(path);
  else if (nLambda(base))
    lbNew.push_back(path);
  else if (nApp(base))
    atNew.push_back(path);
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

    atComposeFromList(lbPrev, atPrev);
    atComposeFromList(lbPaths, atPrev);
    atComposeFromList(lbPrev, atPaths);

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

Node* copyTerm(Node* org, Node* dst)
{
  if (org == NULL)
    return NULL;

  if (nApp(org))
  {
    dst->abt = copyTerm(org->abt, mknode());
    dst->arg = copyTerm(org->arg, mknode());
  }
  else if (nLambda(org))
  {
    dst->isLambda = true;
    dst->var = org->var;
    dst->abt = copyTerm(org->abt, mknode());
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
      cr->arg = copyTerm(nterm, mknode());
      cr = cr->abt;
    }

    cr->abt = nterm;
    cr->arg = qterm;
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
        cr = cr->abt;
      }
    }

    cleanup(fn, base, 1);
    cr->abt = fn;
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

  printf("%s: (%s, %s) - ", p.c_str(), p.back().c_str(), p.front().c_str());
  printf("%d of %s", num, n->var.c_str());
  printf(" not");
  printf(" linear\n");
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

  labelTerm(term, 'a');

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
    bool linear = false;
    int iter;

    while (!linear)
    {
      linear = true;
      
      labelNode.clear();
      labelTerm(term, 'a');
      iter = fillPaths(term);

      for (int i = 0; i < iter; i++)
        for (auto path : S[i])
          if (notLinear(path))
          {
            linearize(path, term);
            //linear = false;
            goto reset;
          }

    reset:
      ;
    }

    labelTerm(term, 'a');

    printTerm(term, 0);
    printf("\n");

    printTerm(term, 1);
    printf("\n");

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

  return 0;
}
