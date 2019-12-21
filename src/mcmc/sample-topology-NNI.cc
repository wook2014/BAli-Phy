/*
  Copyright (C) 2004-2009 Benjamin Redelings

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

#include <valarray>
#include <iostream>
#include <cmath>
#include "util/assert.hh"
#include "sample.H"
#include "probability/choose.H"
#include "util/rng.H"
#include "dp/5way.H"
#include "dp/alignment-sums.H"
#include "alignment/alignment-util.H"
#include "tree/tree-util.H"

#include "dp/3way.H"
#include "sample.H"

using MCMC::MoveStats;
using std::string;
using std::vector;

// We are sampling from a 5-way alignment (along 5 branches)

// Its a 4-way dynamic programming, though - so the only thing
// that matters is the order of the 4D path. (I think...)

// We want to scramble the sorting method for the branches
// Perhaps that should be the NEXT step?  We can scramble the
// node names, though - we use those to know which leaf node
// is connected to which internal node.

// Branches are labelled 0-3, as are the leaves.  Internal nodes
// are 4,5; internal branch is 5.

using std::abs;
using std::valarray;

using namespace A5;


/// Update statistics counters for an NNI move.
void NNI_inc(MoveStats& Stats, const string& name, MCMC::Result result,double L)
{
    Stats.inc(name, result);

    if (L < 0.0325)
	Stats.inc(name+"-0.0325", result);
    else if (L < 0.065)
	Stats.inc(name+"-0.065", result);
    else if (L < 0.125)
	Stats.inc(name+"-0.125", result);
    else if (L < 0.25)
	Stats.inc(name+"-0.25", result);
    else if (L < 0.5)
	Stats.inc(name+"-0.5", result);
    else if (L < 1)
	Stats.inc(name+"-1.0", result);
    else if (L < 2.0)
	Stats.inc(name+"-2.0", result);
    else
	Stats.inc(name+"-2.0+", result);
}

// Do we need the different sample_two_nodes_base routines to use the same
// sub-alignment ordering for different topologies?  No.
//  o Sub-alignment order should affect only which paths are considered
//  o We are essentially considering a set of paths for each topology
//    (So have ALMOST marginalized over the paths: we don't consider some column orders though)
//  o We then divide them up unto groups (topologies)
//  o 1st choose between the groups ,
//  o 2nd choose between the paths in the chosen group.
// The fact that we don't consider some paths should not make this non-reversible
// Each combination of order for each topology is a reversible move, because each path proposes the others.

///Sample between 2 topologies, ignoring gap priors on each case

int two_way_topology_sample(vector<Parameters>& p,const vector<log_double_t>& rho, int b) 
{
    vector< A5::hmm_order > orders(2);
    orders[0] = A5::get_nodes_random(p[0].t(), b);
    orders[1] = A5::get_nodes_random(p[1].t(), b);

    try {
	return sample_two_nodes_multi(p,orders,rho,true,false);
    }
    catch (choose_exception<log_double_t>& c)
    {
	c.prepend(__PRETTY_FUNCTION__);
	throw c;
    }
}


#include "slice-sampling.H"

// Notes: the two-say slice sampler is more likely to accept topologies
//        which have a low probability without branch adjustment.
//        
//        If we look at the distribution for accepted changes of
//        log(P2)-log(P1) without adjusting the branch lengths,
//        then 1% are below -3.23 for MH and -6.3 for slice.

//        Also, 2% are below -5.19 for slice, adjusting for the fact
//        that there are fewer (half?) acceptances for slice.

//        Finally, the bottom 5% for slice make up the bottom .7%
//        (unadjusted) for slice...

//        Experiment #1: load in a posterior sample, to find out what the acceptance
//                       probability *should* be based only on the relative probabilities
//                       of the topologies.
//
//        Experiment #2: for each proposal, do a long MCMC chain where we consider only two
//                       topologies but allow branch lengths to vary, in order to find out
//                       what the acceptance probability should be.

// check the HMM type for a DIRECTED branch without going off the end of the array
int HMM_type_for_branch(const Parameters& P, int b)
{
    return P.branch_HMM_type(P.t().undirected(b));
}

void two_way_topology_slice_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1) return;

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;

    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);

    vector<Parameters> p(2,PP);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);
  
    //  if (not extends(p[1].t(), PP.PC->TC))
    //    return;

    double L = PP.t().branch_length(b);

    //  We cannot evaluate Pr2 here unless -t: internal node states could be inconsistent!
    //  double Pr1 = log(p[0].probability());
    //  double Pr2 = log(p[1].probability());

    branch_length_slice_function logp1(p[0],b);
    branch_length_slice_function logp2(p[1],b);

    vector<slice_function*> logp;
    logp.push_back(&logp1);
    logp.push_back(&logp2);

    double w = PP.branch_mean();

    //  std::pair<int,double> choice = two_way_slice_sample(L,logp1,logp2,w,-1,true,0,false,0);
    std::pair<int,double> choice = slice_sample_multi(L,logp,w,-1);

    int C = choice.first;
    if (C == -1) return;

    if (choice.first == 0)
	PP = p[0];
    else
	PP = p[1];

    MCMC::Result result(3);

    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = L;
    else
	result.counts[1] = 0;
    result.totals[2] = std::abs(PP.t().branch_length(b) - L);

    //  if (C == 1) std::cerr<<"slice-diff = "<<Pr2 - Pr1<<"\n";

    NNI_inc(Stats,"NNI (2-way,slice)", result, L);
}

void two_way_topology_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1) return;

    double slice_fraction = PP.load_value("NNI_slice_fraction",-0.25);

    if (not PP.variable_alignment() and uniform() < slice_fraction) {
	two_way_topology_slice_sample(P,Stats,b);
	return;
    }

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;

    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);

    vector<Parameters> p(2,PP);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);
  
    //  if (not extends(p[1].t(), PP.PC->TC))
    //    return;

    //  We cannot evaluate Pr2 here unless -t: internal node states could be inconsistent!
    //  double Pr1 = log(p[0].probability());
    //  double Pr2 = log(p[1].probability());

    vector<log_double_t> rho(2,1);

    // Because we would select between topologies before selecting
    // internal node states, the reverse distribution cannot depend on 
    // the internal node state of the proposed new topology/alignment

    vector< A5::hmm_order > orders(2);
    orders[0] = A5::get_nodes_random(p[0].t(), b);
    orders[1] = A5::get_nodes_random(p[1].t(), b);

    bool smart = (uniform() < 0.5);
    if (smart)
    {
	//    std::cerr<<"order = "<<order.nodes<<"\n";
	orders[0] = order;
	orders[0].topology = 0;
	std::swap(orders[0].nodes[2], orders[0].nodes[3]);
	vector<int> v1 = {orders[0].nodes[0],
			  orders[0].nodes[1],
			  orders[0].nodes[2],
			  orders[0].nodes[3]};
    
	//    std::cerr<<"v1 = "<<v1<<"\n";
	orders[1] = order;
	std::swap(orders[1].nodes[1], orders[1].nodes[2]);
	orders[1].topology = 1;
	vector<int> v2 = {orders[1].nodes[0],
			  orders[1].nodes[2],
			  orders[1].nodes[3],
			  orders[1].nodes[1]};

	//    std::cerr<<"v2 = "<<v2<<"\n";
	assert(v1 == v2);
    }

    int C = -1;
    try {
	C = sample_two_nodes_multi(p,orders,rho,true,false);
    }
    catch (choose_exception<log_double_t>& c)
    {
	c.prepend(__PRETTY_FUNCTION__);
	throw c;
    }

    if (C != -1) {
	PP = p[C];
    }

    //  if (C == 1) std::cerr<<"MH-diff = "<<Pr2 - Pr1<<"\n";

    MCMC::Result result(2);

    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = p[0].t().branch_length(b);
    else
	result.counts[1] = 0;

    if (smart)
	NNI_inc(Stats,"NNI (2-way smart)", result, p[0].t().branch_length(b));
    else
	NNI_inc(Stats,"NNI (2-way stupid)", result, p[0].t().branch_length(b));
}

void two_way_NNI_SPR_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1) return;

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;

    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);

    vector<Parameters> p(2,PP);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);
  
    //  if (not extends(p[1].t(), PP.PC->TC))
    //    return;

    double LA = p[0].t().branch_length(p[0].t().find_branch(nodes[4],nodes[0]));
    double LB = p[0].t().branch_length(p[0].t().find_branch(nodes[4],nodes[5]));
    double LC = p[0].t().branch_length(p[0].t().find_branch(nodes[5],nodes[3]));

    p[1].setlength(p[1].t().find_branch(nodes[0],nodes[4]),LA + LB);
    p[1].setlength(p[1].t().find_branch(nodes[4],nodes[5]),LC*uniform());
    p[1].setlength(p[1].t().find_branch(nodes[5],nodes[3]),LC - p[1].t().branch_length(p[0].t().find_branch(nodes[4],nodes[5])));

    vector<log_double_t> rho(2,1);
    rho[1] = LC/(LA+LB);

    int C = two_way_topology_sample(p,rho,b);

    if (C != -1) {
	PP = p[C];
    }


    MCMC::Result result(2);

    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = p[0].t().branch_length(b);
    else
	result.counts[1] = 0;
    NNI_inc(Stats,"NNI (2-way/SPR)", result, p[0].t().branch_length(b));
}

vector<int> NNI_branches(const TreeInterface& t, int b) 
{
    vector<int> branches;
    branches.push_back(b);

    t.append_branches_after(b, branches);
    t.append_branches_before(b, branches);

    assert(branches.size() == 5);

    return branches;
}

void two_way_NNI_and_branches_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1) return;

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;

    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);

    vector<Parameters> p(2,PP);

    //---------------- Do the NNI operation -------------------//
    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);
  
    //  if (not extends(p[1].t(), PP.PC->TC))
    //    return;

    //------------- Propose new branch lengths ----------------//
    log_double_t ratio = 1.0;
    vector<int> branches = NNI_branches(p[1].t(), b);

    for(int i=0;i<branches.size();i++) {

	auto factor = exp_to<log_double_t>(gaussian(0,0.05));

	double L = p[1].t().branch_length( branches[i] ) * factor;

	p[1].setlength(branches[i], L);

	ratio *= factor;
    }


    vector<log_double_t> rho(2);
    rho[0] = 1.0;
    rho[1] = ratio;

    int C = two_way_topology_sample(p,rho,b);

    if (C != -1) {
	PP = p[C];
    }

    MCMC::Result result(2);

    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = p[0].t().branch_length(b);
    else
	result.counts[1] = 0;

    NNI_inc(Stats,"NNI (2-way) + branches", result, p[0].t().branch_length(b));
}

void two_way_NNI_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1) return;

    double U = uniform();
    if (U < 0.33333333) {
	two_way_topology_sample(P,Stats,b);
    }
    else if (U < 0.66666666)
	two_way_NNI_SPR_sample(P,Stats,b);
    else
	two_way_NNI_and_branches_sample(P,Stats,b);
}

void three_way_topology_sample_slice(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment()) return;

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;

    //------ Generate Topologies and alter caches ------///
    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);
    int b3 = PP.t().find_branch(nodes[5],nodes[3]);

    vector<Parameters> p(3,PP);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);

    // Internal node states may be inconsistent after this: p[2].alignment_prior() undefined!
    p[2].NNI(b1, b3);

    const vector<log_double_t> rho(3,1);

    double L = PP.t().branch_length(b);

#ifndef NDEBUG
    //  We cannot evaluate Pr2 here unless -t: internal node states could be inconsistent!
    log_double_t Pr1 = p[0].heated_probability();
    log_double_t Pr2 = p[1].heated_probability();
    log_double_t Pr3 = p[2].heated_probability();
#endif

    branch_length_slice_function logp1(p[0],b);
    branch_length_slice_function logp2(p[1],b);
    branch_length_slice_function logp3(p[2],b);

#ifndef NDEBUG
    assert(std::abs(Pr1.log() - logp1(L)) < 1.0e-9);
    assert(std::abs(Pr2.log() - logp2(L)) < 1.0e-9);
    assert(std::abs(Pr3.log() - logp3(L)) < 1.0e-9);
#endif

    vector<slice_function*> logp;
    logp.push_back(&logp1);
    logp.push_back(&logp2);
    logp.push_back(&logp3);

    double w = PP.branch_mean();

    std::pair<int,double> choice = slice_sample_multi(L,logp,w,-1);

    int C = choice.first;
    if (C != -1)
	PP = p[C];

    MCMC::Result result(4);

    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = L;
    else
	result.counts[1] = 0;
    result.totals[2] = std::abs(PP.t().branch_length(b) - L);
    result.totals[3] = logp1.count + logp2.count + logp3.count;

    //  if (C == 1) std::cerr<<"slice-diff3 = "<<Pr2 - Pr1<<"\n";
    //  if (C == 2) std::cerr<<"slice-diff3 = "<<Pr3 - Pr1<<"\n";

    // stats are here mis-reported!
    NNI_inc(Stats,"NNI (3-way,slice)", result, L);
}

void three_way_topology_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1)
	return;

    double slice_fraction = PP.load_value("NNI_slice_fraction",-0.25);

    if (not PP.variable_alignment() and uniform() < slice_fraction) {
	three_way_topology_sample_slice(P,Stats,b);
	return;
    }

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& nodes = order.nodes;
    PP.select_root(b);
    PP.likelihood();

    int b1 = PP.t().find_branch(nodes[4],nodes[1]);
    int b2 = PP.t().find_branch(nodes[5],nodes[2]);
    int b3 = PP.t().find_branch(nodes[5],nodes[3]);

    //------ Generate Topologies and alter caches ------///
    vector<Parameters> p(3,PP);

    double L0 = PP.t().branch_length(b);

    vector< A5::hmm_order > orders(3);
    orders[0] = A5::get_nodes_random(p[0].t(), b);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2);
    orders[1] = A5::get_nodes_random(p[1].t(), b);

    // Internal node states may be inconsistent after this: p[2].alignment_prior() undefined!
    p[2].NNI(b1, b3);
    orders[2] = A5::get_nodes_random(p[2].t(), b);
  
    const vector<log_double_t> rho(3,1);

    //------ Resample alignments and select topology -----//

    try {
	int C = sample_two_nodes_multi(p,orders,rho,true,false);

        if (C != -1) {
            PP = p[C];
        }

        MCMC::Result result(2);

        result.totals[0] = (C>0)?1:0;
        // This gives us the average length of branches prior to successful swaps
        if (C>0)
            result.totals[1] = L0;
        else
            result.counts[1] = 0;

        NNI_inc(Stats,"NNI (3-way)", result, L0);
    }
    catch (choose_exception<log_double_t>& c)
    {
	c.prepend(__PRETTY_FUNCTION__);
	throw c;
    }
}

void three_way_topology_and_alignment_sample(owned_ptr<Model>& P, MoveStats& Stats, int b) 
{
    Parameters& PP = *P.as<Parameters>();
    if (PP.t().is_leaf_branch(b)) return;

    if (PP.variable_alignment() and HMM_type_for_branch(PP,b) == 1)
	return;

    A5::hmm_order order = A5::get_nodes_random(PP.t(), b);
    const auto& two_way_nodes = order.nodes;

    //--------- Generate the Different Topologies -------//
    // We ALWAYS resample the connection between two_way_nodes [0] and [4].
    PP.likelihood();

    double L0 = PP.t().branch_length(b);

    PP.select_root(b);
    // PP.likelihood();  Why does this not make a difference in speed?

    int b1 = PP.t().find_branch(two_way_nodes[4],two_way_nodes[1]);
    int b2 = PP.t().find_branch(two_way_nodes[5],two_way_nodes[2]);
    int b3 = PP.t().find_branch(two_way_nodes[5],two_way_nodes[3]);

    vector<Parameters> p(3,PP);

    // Internal node states may be inconsistent after this: p[1].alignment_prior() undefined!
    p[1].NNI(b1, b2, true);

    // Internal node states may be inconsistent after this: p[2].alignment_prior() undefined!
    p[2].NNI(b1, b3, true);

    vector< vector< int> > nodes;
    for(int i=0;i<p.size();i++)
	nodes.push_back(A3::get_nodes_branch_random(p[i].t(), two_way_nodes[4], two_way_nodes[0]) );

    const vector<log_double_t> rho(3,1);

    int C = -1;
    try {
	C = sample_tri_multi(p,nodes,rho,true,true);
    }
    catch (choose_exception<log_double_t>& c)
    {
	c.prepend(__PRETTY_FUNCTION__);
	throw c;
    }

    if (C != -1) {
	PP = p[C];
    }
    
    MCMC::Result result(2);
    
    result.totals[0] = (C>0)?1:0;
    // This gives us the average length of branches prior to successful swaps
    if (C>0)
	result.totals[1] = L0;
    else
	result.counts[1] = 0;
  
    NNI_inc(Stats,"NNI (3-way) + A", result, L0);
}
