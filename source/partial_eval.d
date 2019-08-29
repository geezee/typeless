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
module partial_eval;

import lambdacalc;

Term* partialEval(alias beta, alias dup)(Term* term, ref Env env, DFunc interfunc, int depth) {
    import std.stdio : writefln;

    Term* partialEvalVar(Term* term, ref Env env) {
        // Rule: VAR-1
        if ((term.a in env) !is null)
            return partialEval!(beta,dup)(dup(env[term.a]), env, interfunc, depth);
        // Rule: VAR-2
        return term;
    }

    Term* partialEvalAbs(Term* term, ref Env env) {
        // Rule: ABS
        term = alpha!(beta,dup)(term);
        term.t1 = partialEval!(beta,dup)(term.t1, env, interfunc, depth+1);
        return term;
    }

    Term* partialEvalApp(Term* term, ref Env env) {
        // Rule: APP-ABS
        if (term.t1.type == TType.ABS) {
            term.t1 = alpha!(beta,dup)(term.t1);
            term.t1.t1 = beta!dup(term.t1.t1, term.t1.a, term.t2);
            return partialEval!(beta,dup)(term.t1.t1, env, interfunc, depth);
        }
        // Rule: APP-VAR-*
        else if (term.t1.type == TType.VAR) {
            term.t2 = partialEval!(beta,dup)(term.t2, env, interfunc, depth+1);
            // Rule: APP-VAR-3
            if ((term.t1.a in env) is null
                    || (term.t2.type != TType.ABS && term.t2.type != TType.VAR)) {
                return term;
            }
            // Rule: APP-VAR-2
            else if (env[term.t1.a].type != TType.ABS) { // e' not a value
                term.t1 = dup(env[term.t1.a]);
                return partialEval!(beta,dup)(term, env, interfunc, depth);
            }
            // Rule: APP-VAR-1
            else {
                Term* bdy = alpha!(beta,dup)(dup(env[term.t1.a])); // bdy is ABS
                if (term.t2.type == TType.ABS)  {
                    string newname = "[" ~ term.t1.a ~ "_" ~ term.t2.toString ~ "]";
                    env[newname] = partialEval!(beta,dup)(new Term(TType.APP, null, bdy, term.t2), env, interfunc, depth+1);
                    return partialEval!(beta,dup)(new Term(TType.VAR, newname), env, interfunc, depth);
                } else if (term.t2.type == TType.VAR) {
                    bdy.t1 = beta!dup(bdy.t1, bdy.a, term.t2);
                    return partialEval!(beta,dup)(bdy.t1, env, interfunc, depth);
                } else assert(false);
            }
        } else {
            Term* pt1 = term.t1;
            Term* pt2 = term.t2;
            term.t1 = partialEval!(beta,dup)(term.t1, env, interfunc, depth+1);
            if (pt1 !is term.t1) {
                return partialEval!(beta,dup)(term, env, interfunc, depth);
            } else {
                interfunc(term, depth);
                term.t2 = partialEval!(beta,dup)(term.t2, env, interfunc, depth+1);
                if (pt2 is term.t2) return term;
                else return partialEval!(beta,dup)(term, env, interfunc, depth);
            }
        }
    }

    interfunc(term, depth);
    final switch(term.type) {
        case TType.VAR: return partialEvalVar(term, env);
        case TType.ABS: return partialEvalAbs(term, env);
        case TType.APP: return partialEvalApp(term, env);
    }
}
