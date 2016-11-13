#include <bits/stdc++.h>

using namespace std;

#define MXTERM 1000

struct Node
{
  bool isLambda;
  bool isVar;
  char var, label;
  Node *abt, *arg, *par;
};

char input[MXTERM];
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

bool isVar(char s)
{
  return (s >= 'a') && (s <= 'z');
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

      nextChar();
      curChar(')');
    }
    else if (s == ')' || s == '\0')
    {
      cur--;
      break;
    }
    else
      serror("invalid character");
  }

  return root;
}

void printTerm(Node* cur)
{
  if (cur == NULL)
    return;

  if (cur->isVar)
    printf("%c", cur->var);
  else if (cur->isLambda)
  {
    printf("(\\%c.", cur->var);
    printTerm(cur->abt);
    printf(")");
  }
  else
  {
    printTerm(cur->abt);
    printTerm(cur->arg);
  }
}

char labelTerm(Node* cur, char label)
{
  if (cur == NULL)
    return label;

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

  return 0;
}
