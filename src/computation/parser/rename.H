#ifndef RENAME_H
#define RENAME_H

#include <set>
#include <string>
#include "computation/expression/expression_ref.H"

class Module;

std::string get_func_name(const expression_ref& decl);
std::set<std::string> find_bound_vars(const expression_ref& E);
bool is_pattern_binding(const expression_ref& decl);
bool is_function_binding(const expression_ref& decl);

expression_ref rename_infix_top(const Module& p, const expression_ref&);
expression_ref rename_infix(const Module& p, const expression_ref&);
expression_ref rename(const Module& p, const expression_ref&);
expression_ref rename(const Module& p, const expression_ref&,const std::set<std::string>&);

#endif
