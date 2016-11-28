#include <bits/stdc++.h>

using namespace std;

#define MXTERM 1000
#define MXLABEL 50

struct Node
{
  bool isLambda;
  bool isVar;
  char var, label;
  Node *abt, *arg, *par;
};

typedef string Path;

char input[MXTERM];
Node* labelNode[MXLABEL];
vector<Path> atPaths, lbPaths, vrPaths;
vector<Path> atNew, lbNew, vrNew;
vector<Path> atPrev, lbPrev, vrPrev;
int cur;

Node* mknode()
{
  Node* n = new Node();
  n->isLambda = false;
  n->isVar = false;
  return n;
}

void serror(const char* msg)
{
  fprintf(stderr, "Error on col %d: %s\n", cur + 1, msg);
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

string reverse(string s)
{
  string ns = s;
  reverse(ns.begin(), ns.end());
  return ns;
}

bool curChar(char val)
{
  return val == input[cur];
}

char curChar()
{
  return input[cur];
}

char nextChar()
{
  char s = curChar();
  cur++;
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

      c->abt = parseTerm();
      if (c->abt == NULL)
        serror("invalid lambda content");
      c->abt->par = c;

      rewire(root, cur, r);
    }
    else if (isVar(s))
    {
      Node* r = mknode();
      r->isVar = true;
      r->var = s;

      rewire(root, cur, r);
    }
    else if (s == '(')
    {
      Node* r = parseTerm();
      if (r == NULL)
        serror("invalid parenthesis expression");

      rewire(root, cur, r);

      curChar(')');
    }
    else if (s == ')' || s == '\0')
      break;
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
    printf("%c", cur->var);
    if (pLabel)
      printf("^%c)", cur->label);
  }
  else if (cur->isLambda)
  {
    printf("(\\%c.", cur->var);
    printTerm(cur->abt, pLabel);
    printf(")");
    if (pLabel)
      printf("^%c", cur->label);
  }
  else
  {
    if (pLabel)
      printf("(");
    printTerm(cur->abt, pLabel);
    printTerm(cur->arg, pLabel);
    if (pLabel)
      printf(")^%c", cur->label);
  }
}

char labelTerm(Node* cur, char label)
{
  if (cur == NULL)
    return label;

  labelNode[label - 'a'] = cur;

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
  Node* base = labelNode[path.back() - 'a'];

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
    string path = "";
    path += base->label;

    addPath(path);

    initialPaths(cur->abt);
    initialPaths(cur->arg);
  }  
}

void lambdaCompose(Path lpath, Path vpath)
{
  Node* lnode = labelNode[lpath.back() - 'a'];
  Node* vnode = labelNode[vpath.back() - 'a'];

  if (lnode->var != vnode->var)
    return;

  printf("\\ composing %s with %s\n", lpath.c_str(), vpath.c_str());

  string result = "";
  result += labelNode[lpath.front() - 'a']->par->arg->label;

  Path npath = vpath + reverse(lpath) + result;
  addPath(npath);
}

void atCompose(Path lpath, Path apath)
{
  Node* lnode = labelNode[lpath.back() - 'a'];
  Node* lnode2 = labelNode[lpath.front() - 'a'];
  Node* anode = labelNode[apath.back() - 'a'];

  if (lnode2->par != anode)
    return;

  printf("@ composing %s with %s\n", lpath.c_str(), apath.c_str());

  string result = "";
  result += lnode->abt->label;

  Path npath = apath + lpath + result;
  addPath(npath);
}

void printPaths()
{
  printf("@-paths:\n");
  for (auto path : atPaths)
    printf("%s\n", path.c_str());
  for (auto path : atPrev)
    printf("%s\n", path.c_str());

  printf("\n\\-paths:\n");
  for (auto path : lbPaths)
    printf("%s\n", path.c_str());
  for (auto path : lbPrev)
    printf("%s\n", path.c_str());

  printf("\nv-paths:\n");
  for (auto path : vrPaths)
    printf("%s\n", path.c_str());
  for (auto path : vrPrev)
    printf("%s\n", path.c_str());
}

int main()
{
  scanf(" %s", input);

  cur = 0;
  Node* term = parseTerm();
  if (term == NULL)
    serror("malformed expression");

  printTerm(term);
  printf("\n");

  labelTerm(term, 'a');

  printTerm(term, 1);
  printf("\n");

  scanf("%*c");

  initialPaths(term);
  int changes = !atNew.empty() || !lbNew.empty() || !vrNew.empty();

  for (auto path : atNew)
    atPrev.push_back(path);

  for (auto path : lbNew)
    lbPrev.push_back(path);

  for (auto path : vrNew)
    vrPrev.push_back(path);
  atNew.clear(), lbNew.clear(), vrNew.clear();

  while (changes)
  {
    printPaths();
    printf("\n");

    for (auto lpath : lbPrev)
      for (auto vpath : vrPrev)
        lambdaCompose(lpath, vpath);

    for (auto lpath : lbPaths)
      for (auto vpath : vrPrev)
        lambdaCompose(lpath, vpath);

    for (auto lpath : lbPrev)
      for (auto vpath : vrPaths)
        lambdaCompose(lpath, vpath);

    for (auto lpath : lbPrev)
      for (auto apath : atPrev)
        atCompose(lpath, apath);

    for (auto lpath : lbPaths)
      for (auto apath : atPrev)
        atCompose(lpath, apath);

    for (auto lpath : lbPrev)
      for (auto apath : atPaths)
        atCompose(lpath, apath);

    changes = !atNew.empty() || !lbNew.empty() || !vrNew.empty();

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
    atNew.clear(), lbNew.clear(), vrNew.clear();
  }

  return 0;
}
