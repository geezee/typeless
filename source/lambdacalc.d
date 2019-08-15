module lambdacalc;

import std.ascii : isWhite;
import std.array : replace, split;


enum TType { VAR, APP, ABS };


struct Term {
    TType type;
    string a;
    Term* t1;
    Term* t2;
}


alias Env = Term*[string];


string toString(Term* t) {
    if (t == null) return ".";
    if (t.type == TType.VAR) return t.a;
    if (t.type == TType.ABS) return "^" ~ t.a ~ "." ~ t.t1.toString;
    if (t.type == TType.APP) return "(" ~ t.t1.toString ~ " " ~ t.t2.toString ~ ")";
    return "";
}


Term* parse(string s) {
    string[] tokens = s.replace("(", " ( ").replace(")", " ) ").replace("'", " ' ").split!isWhite;
    Term*[] stack = [];

    void fillStackHole() {
        if (stack.length < 2) return;
        Term* parent = stack[$-2];
        Term* front = stack[$-1];
        final switch (parent.type) {
            case TType.APP:
                if (parent.t1 == null) { parent.t1 = front; break; }
                else if (parent.t2 == null) { parent.t2 = front; break; }
                goto case;
            case TType.ABS:
                if (parent.t1 == null) { parent.t1 = front; break; }
                goto case;
            case TType.VAR:
                stack[$-2] = new Term(TType.APP, null, parent, front);
        }
        stack = stack[0..$-1];
    }

    for (int i=0; i < tokens.length; i++) {
        string token = tokens[i];
        if (token.length == 0) continue;
        if (token == "(") {
            if(tokens[i+1] != "lambda") stack ~= new Term(TType.APP);
        } else if (token == "lambda")  {
            stack ~= new Term(TType.ABS, tokens[i+1]);
            i++; // skip the var
        } else if (token == ")") fillStackHole();
        else { stack ~= new Term(TType.VAR, token); fillStackHole(); }
    }

    assert (stack.length == 1, "unbalanced parans");
    return stack[0];
}
