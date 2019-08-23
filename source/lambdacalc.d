/*
Copyright 2019 - George Zakhour

This file is part of typeless.git

typeless.git is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

typeless.git is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with typeless.git. If not, see <https://www.gnu.org/licenses/>.
*/
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

alias DFunc = void delegate(Term*, int);


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


// used for alpha reduction
ulong counter = 0;

// invariant: variable at nameHistory[index] was replaced with _?index
string[] nameHistory = [];

Term* alpha(alias beta)(Term* term)
in {
    assert(term.type == TType.ABS);
}
body {
    import std.conv : to;
    string varName = "_?" ~ counter.to!string;
    term.t1 = beta(term.t1, term.a, new Term(TType.VAR, varName));
    nameHistory ~= term.a;
    term.a = varName;
    counter++;
    return term;
}

// replace all _?index variables by their original name (may introduce confusion)
Term* unalpha(Term* term) {
    import std.conv : to;
    import std.string : isNumeric;
    final switch (term.type) {
        case TType.VAR:
            while (term.a.length > 2 && term.a[0..2] == "_?" && term.a[2..$].isNumeric) {
                term.a = nameHistory[term.a[2..$].to!size_t];
            }
            return term;
        case TType.ABS:
            while (term.a.length > 2 && term.a[0..2] == "_?" && term.a[2..$].isNumeric) {
                term.a = nameHistory[term.a[2..$].to!size_t];
            }
            term.t1 = unalpha(term.t1);
            return term;
        case TType.APP:
            term.t1 = unalpha(term.t1);
            term.t2 = unalpha(term.t2);
            return term;
    }
}
