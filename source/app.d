import std.stdio;
import std.string : strip;
import std.range : repeat;
import std.file : readText;
import std.conv : text;
import std.algorithm.iteration : joiner;
import std.algorithm.searching : count;
import std.getopt;

import lambdacalc;
import dups;
import betas;
import evals;

bool debugMode = false;
bool doEvalOpt = false;
bool doBetaOpt = false;
bool doDupOpt = false;
bool useCustomStack = false;
string source = "";

Env env;

void handle(string exprs) {
    ulong evalCount = 0;

    void delegate(Term*,int) debugCont = (Term* step, int depth) {
        writefln("  >%s %s", ">".repeat(depth).joiner(""), toString(step));
        evalCount++;
    };
    void delegate(Term*,int) normalCont = (Term* step, int depth) {
        evalCount++;
    };

    auto cont = debugMode ? debugCont : normalCont;

    foreach (expr; exprs.split(";")) {
        if (expr.length == 0) continue;
        string[] tokens = expr.split("=");
        try
            if (tokens.length > 1)
                env[tokens[0].strip] = parse(tokens[1..$].joiner("=").text);
            else if (tokens.length == 1 && tokens[0].strip.length > 0) {
                Term* t;
                if (useCustomStack) {
                    auto betaStack = new Stack!(BetaData*)();
                    auto evalStack = new Stack!(EvalData*)();
                    auto dupStack = new Stack!(DupData*)();
                    auto betaFun = (Term* t, string v, Term* val) { return betaOptStack(t, v, val, betaStack); };
                    auto dupFun = (Term* t) { return dupOptStack(t, dupStack); };
                    if (doEvalOpt) if (doBetaOpt) if (doDupOpt) t = evalOptStack!(betaFun,dupFun)(expr.parse, env, cont, 0, evalStack);
                                                  else          t = evalOptStack!(betaFun,dup)(expr.parse, env, cont, 0, evalStack);
                                   else           if (doDupOpt) t = evalOptStack!(beta,dupFun)(expr.parse, env, cont, 0, evalStack);
                                                  else          t = evalOptStack!(beta,dup)(expr.parse, env, cont, 0, evalStack);
                    else           if (doBetaOpt) if (doDupOpt) t = eval!(betaFun, dupFun)(expr.parse, env, cont);
                                                  else          t = eval!(betaFun,dup)(expr.parse, env, cont);
                                   else           if (doDupOpt) t = eval!(beta,dupFun)(expr.parse, env, cont);
                                                  else          t = eval!(beta,dup)(expr.parse, env, cont);
                } else {
                    if (doEvalOpt) if (doBetaOpt) if (doDupOpt) t = evalOpt!(betaOpt,dupOpt)(expr.parse, env, cont);
                                                  else          t = evalOpt!(betaOpt,dup)(expr.parse, env, cont);
                                   else           if (doDupOpt) t = evalOpt!(beta,dupOpt)(expr.parse, env, cont);
                                                  else          t = evalOpt!(beta,dup)(expr.parse, env, cont);
                    else           if (doBetaOpt) if (doDupOpt) t = eval!(betaOpt, dupOpt)(expr.parse, env, cont);
                                                  else          t = eval!(betaOpt,dup)(expr.parse, env, cont);
                                   else           if (doDupOpt) t = eval!(beta,dupOpt)(expr.parse, env, cont);
                                                  else          t = eval!(beta,dup)(expr.parse, env, cont);
                }
                writeln(t.toString);
                writefln("\t%d reductions", evalCount);
                evalCount = 0;
            }
        catch (Exception e) writefln("error: %s", e.msg);
        catch (Error e) writefln("error: %s", e.msg);
    }
}

void main(string[] args) {
    getopt(
        args,
        "debug", &debugMode,
        "e", &doEvalOpt,
        "b", &doBetaOpt,
        "d", &doDupOpt,
        "s", &useCustomStack
    );
    if (args.length > 1) source = args[1];


    if (source.length > 0) {
        handle(source.readText ~ "; main");
    } else {
        string exprs = "";
        do {
            writef("\r%s> ", exprs.length == 0 ? "" : ">");
            exprs ~= readln();
            if (exprs.length == 0) return;
            size_t openParans = exprs.count("(") - exprs.count(")");
            if (openParans == 0) {
                handle(exprs);
                exprs = "";
            } else if (openParans < 0) {
                writefln("error: unbalanced parans");
                exprs = "";
            }
        } while(true);
    }
}
