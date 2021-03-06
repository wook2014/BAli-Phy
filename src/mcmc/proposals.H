/*
  Copyright (C) 2006-2010 Benjamin Redelings

  This file is part of BAli-Phy.

  BAli-Phy is free software; you can redistribute it and/or modify it under
  the terms of the GNU General Public License as published by the Free
  Software Foundation; either version 2, or (at your option) any later
  version.

  BAli-Phy is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
  for more details.

  You should have received a copy of the GNU General Public License
  along with BAli-Phy; see the file COPYING.  If not see
  <http://www.gnu.org/licenses/>.  */

#ifndef PROPOSALS_H
#define PROPOSALS_H

#include <functional>              // for function
#include <string>                  // for string
#include <vector>                  // for vector
#include "computation/object.H"    // for Object
#include "util/bounds.H"           // for bounds
#include "util/math/log-double.H"  // for log_double_t
class context_ref;
class expression_ref;

log_double_t scale_gaussian(double& x,double sigma);

typedef std::function<log_double_t(context_ref& P)> Proposal;

// This type of proposal can't check if arguments are fixed, and therefore must assume that they are
// all variable.  Therefore, it can't have any fixed arguments.
typedef std::function<log_double_t(std::vector< expression_ref >& x,const std::vector<double>& p)> proposal_fn;

class less_than
{
    double max;
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    less_than(double m,const proposal_fn& P);
};

class more_than
{
    double min;
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    more_than(double m,const proposal_fn& P);
};

class Between
{
    double min;
    double max;
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    Between(double m1,double m2,const proposal_fn& P);
};

class Reflect
{
    bounds<double> bounds_;
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    Reflect(const bounds<double>& b,const proposal_fn& P);
};

class log_scaled
{
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    log_scaled(const proposal_fn& P);
};

class LOD_scaled
{
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    LOD_scaled(const proposal_fn& P);
};

class sorted
{
    proposal_fn proposal;
public:
    log_double_t operator()(std::vector< expression_ref >& x,const std::vector<double>& p) const;
    sorted(const proposal_fn& P);
};

class Proposal2M
{
    proposal_fn proposal;
    std::vector<int> indices;
    std::vector<double> parameters;

public:
    const std::vector<int>& get_indices() const {return indices;}
    log_double_t operator()(context_ref& P) const;
    Proposal2M(const proposal_fn& p,int, const std::vector<double>& v);
    Proposal2M(const proposal_fn& p,const std::vector<int>&, const std::vector<double>& v);
};


log_double_t dirichlet_proposal(std::vector< expression_ref >& x,const std::vector<double>& p);

log_double_t scale_gaussian2(std::vector< expression_ref >& x,const std::vector<double>& p);

log_double_t shift_gaussian(std::vector< expression_ref >& x,const std::vector<double>& p);

log_double_t shift_laplace(std::vector< expression_ref >& x,const std::vector<double>& p);

log_double_t shift_cauchy(std::vector< expression_ref >& x,const std::vector<double>& p);

log_double_t shift_delta(std::vector< expression_ref >& x, const std::vector<double>& p);

log_double_t shift_epsilon(std::vector< expression_ref >& x, const std::vector<double>& p);

log_double_t bit_flip(std::vector< expression_ref >& x, const std::vector<double>& p);

log_double_t discrete_uniform(std::vector< expression_ref >& x, const std::vector<double>& p);

log_double_t discrete_uniform_avoid(std::vector< expression_ref >& x, const std::vector<double>& p);

log_double_t move_subst_type_branch(context_ref& P);

log_double_t realign_and_propose_parameter(context_ref& P, const std::vector<int>& partitions, const Proposal& propose);

#endif
