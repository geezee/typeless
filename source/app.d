import std.stdio;
import std.array : replace, split;
import std.string : strip;
import std.range : repeat;
import std.algorithm.iteration : joiner;

enum TType { VAR, APP, ABS };

struct Term {
    TType type;
    string a;
    Term* t1;
    Term* t2;
}

alias Env = Term*[string];


bool isValue(Term* term) {
    return term.type == TType.VAR || term.type == TType.ABS;
}

bool hasHoles(Term* t) {
    return (t.type == TType.ABS && t.t1 == null)
        || (t.type == TType.APP && (t.t1 == null || t.t2 == null));
}

string toString(Term* t) {
    if (t == null) return ".";
    if (t.type == TType.VAR) return t.a;
    if (t.type == TType.ABS) return "^" ~ t.a ~ "." ~ t.t1.toString;
    if (t.type == TType.APP) return "(" ~ t.t1.toString ~ " " ~ t.t2.toString ~ ")";
    return "";
}

Term* dup(Term* t) {
    if (t == null) return null;
    return new Term(t.type, t.a, t.t1.dup, t.t2.dup);
}


Term* parse(string s) {
    import std.ascii : isWhite;
    string[] tokens = s.replace("(", " ( ").replace(")", " ) ").split!isWhite;
    int depth = 0;
    Term*[] stack = [];

    void pushToStack(Term* t) {
        if (stack.length == 0 || t.hasHoles) {
            stack ~= t;
        } else {
            Term* front = stack[$-1];
            while (true) {
                if (!front.hasHoles) return;
                if (front.type == TType.ABS) {
                    front.t1 = t;
                } else if (front.type == TType.APP) {
                    if (front.t1 == null) front.t1 = t;
                    else if (front.t2 == null) front.t2 = t;
                }
                if (!front.hasHoles) {
                    t = front;
                    stack = stack[0..$-1];
                    if (stack.length == 0) { stack ~= front; return; }
                    front = stack[$-1];
                } else return;
            }
        }
    }

    for (int i=0; i < tokens.length; i++) {
        string token = tokens[i];
        if (token.length == 0) continue;
        if (token == "(") {
            depth++;
            if(tokens[i+1] != "lambda") pushToStack(new Term(TType.APP));
        } else if (token == "lambda")  {
            pushToStack(new Term(TType.ABS, tokens[i+1]));
            i++; // skip the var
        } else if (token == ")") {
            depth--;
        } else pushToStack(new Term(TType.VAR, token));
    }
    assert (depth == 0, "unbalanced parans");
    return stack[0];
}


Term* beta(Term* term, string var, Term* val) {
    if (term == null) return term;
    if (term.type == TType.VAR && term.a == var) return val.dup;
    if (term.type == TType.ABS) {
        if (term.a == var) return term;
        if (term.t1 == null) {
            writefln("error, can't do that");
            return null;
        } else {
            term.t1 = beta(term.t1, var, val);
            return term;
        }
    } else if (term.t1 != null && term.t2 != null) {
        term.t1 = beta(term.t1, var, val);
        term.t2 = beta(term.t2, var, val);
        return term;
    }
    return term;
}


Term* eval(Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0) {
    interfunc(term, depth);

    if (term.type == TType.VAR) {
        if (term.a == "write") {
            return new Term(TType.VAR, "write");
        } else if ((term.a in env) !is null) {
            return eval(env[term.a], env, interfunc, depth).dup;
        } else return term;
    } else if (term.type == TType.ABS) {
        return term;
    } else if (term.type == TType.APP) {
        if (term.t1.type == TType.ABS) {
            term.t1.t1 = beta(term.t1.t1, term.t1.a, term.t2);
            return eval(term.t1.t1, env, interfunc, depth);
        } else {
            if (term.t1.type == TType.VAR && term.t1.a == "write") {
                writefln(".");
                return eval(term.t2, env, interfunc, depth-1);
            }
            Term* old1 = term.t1;
            Term* old2 = term.t2;
            term.t1 = eval(term.t1, env, interfunc, depth+1);
            term.t2 = eval(term.t2, env, interfunc, depth+1);
            return eval(term, env, interfunc, depth);
        }
    } else return term;
}


void main()
{
    string input = `
        true = lambda t lambda f t;
        false = lambda t lambda f f;

        not = lambda b lambda t lambda f (b f t);
        if = lambda b lambda t lambda f ((b t) f);

        zero = lambda S (lambda z z);
        succ = lambda n (lambda S (lambda z ((n S) (S z))));
        one = (succ zero);
        two = (succ one);
        three = (succ two);
        four = (succ three);
        apply = lambda a lambda b (a f);
        0 = lambda b b;
        main = ((four write) 0)
    `;
    Env env;
    foreach (expr; input.split(";")) {
        string[] tokens = expr.split("=");
        if (tokens.length == 2)
            env[tokens[0].strip] = parse(tokens[1]);
    }
    string[] exprs = input.split(`;`);
    
    foreach (k,v; env) {
        writefln("%s = %s", k, toString(v));
    }

    env["main"].eval(env, (Term* step, int depth) {
        // writefln(">%s %s", ">".repeat(depth).joiner(""), toString(step));
    });
}
