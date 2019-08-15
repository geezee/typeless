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
                if (doEvalOpt) if (doBetaOpt) if (doDupOpt) t = evalOpt!(betaOpt,dupOpt)(expr.parse, env, cont, 0);
                                              else          t = evalOpt!(betaOpt,dup)(expr.parse, env, cont, 0);
                               else           if (doDupOpt) t = evalOpt!(beta,dupOpt)(expr.parse, env, cont, 0);
                                              else          t = evalOpt!(beta,dup)(expr.parse, env, cont, 0);
                else           if (doBetaOpt) if (doDupOpt) t = eval!(betaOpt, dupOpt)(expr.parse, env, cont);
                                              else          t = eval!(betaOpt,dup)(expr.parse, env, cont);
                               else           if (doDupOpt) t = eval!(beta,dupOpt)(expr.parse, env, cont);
                                              else          t = eval!(beta,dup)(expr.parse, env, cont);
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
