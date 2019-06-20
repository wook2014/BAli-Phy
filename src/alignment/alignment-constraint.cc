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

#include <sstream>
#include <iostream>
#include <fstream>
#include <utility>
#include <set>
#include "alignment/alignment-constraint.H"
#include "alignment/alignment-util.H"
#include "tree/tree-util.H"
#include "util/string/split.H"
#include "util/string/convert.H"
#include "util/mapping.H"
#include "util/range.H"
#include "util/set.H"
#include "util/io.H"
#include <optional>                            // for optional
#include "sequence/alphabet.H"                 // for alphabet, alphabet::gap
#include "tree/sequencetree.H"                 // for SequenceTree
#include "util/assert.hh"                      // for assert
#include "util/myexception.H"                  // for myexception

using std::string;
using std::set;
using std::ifstream;
using std::vector;
using std::valarray;
using std::pair;
using boost::get;

using boost::program_options::variables_map;
using boost::dynamic_bitset;
using std::vector;
using std::optional;

vector<optional<int>> get_max_y_le_x(const pairwise_alignment_t& a_xy)
{
    vector<optional<int>> max_y_le_x;

    int y = 0;
    optional<int> last_matched_y;
    for(int i=0;i<a_xy.size();i++)
    {
	if (a_xy.is_match(i)) last_matched_y = y;

	if (a_xy.has_character1(i))
	    max_y_le_x.push_back(last_matched_y);

	if (a_xy.has_character2(i)) y++;
    }

    assert(max_y_le_x.size() == a_xy.length1());

    return max_y_le_x;
}

vector<optional<int>> get_min_y_ge_x(const pairwise_alignment_t& a_xy)
{
    vector<optional<int>> min_y_ge_x;

    int y = 0;
    for(int i=0; i<a_xy.size(); i++)
	if (a_xy.has_character2(i)) y++;

    optional<int> last_matched_y;
    for(int i=int(a_xy.size())-1; i>=0; i--)
    {
	if (a_xy.has_character2(i)) y--;

	if (a_xy.is_match(i)) last_matched_y = y;

	if (a_xy.has_character1(i))
	    min_y_ge_x.push_back(last_matched_y);
    }

    assert(min_y_ge_x.size() == a_xy.length1());
    std::reverse(min_y_ge_x.begin(), min_y_ge_x.end());
    return min_y_ge_x;
}

optional<int> lookup(const vector<optional<int>>& array, const optional<int>& index)
{
    if (index)
	return array[*index];
    else
	return index;
}

vector<int> count_constrained_characters(const matrix<int>& m)
{
    vector<int> counts(m.size1());
    for(int i=0;i<m.size1();i++)
    {
	int count = 0;
	for(int j = 0; j < m.size2(); j++)
	    if (m(i,j) >= 0)
		count++;
	counts[i] = count;
    }
    return counts;
}

pair<matrix<int>,vector<int>> constraint_matrix_from_alignment(const alignment& A, int n)
{
    auto m1 = M(A);
    matrix<int> m2(m1.size1(), n);
    for(int i=0;i<m2.size1();i++)
	for(int j=0;j<m2.size2();j++)
	    m2(i,j) = m1(i,j);
    auto totals = count_constrained_characters(m2);
    return pair<matrix<int>,vector<int>>{m2,totals};
}

vector<pair<int,int>> get_yboundaries_from_cons(int I, int J, const alignment_constraints& x_con, const alignment_constraints& y_con)
{
    vector<pair<int,int>> yboundaries(I+1,pair<int,int>{0,J});
    assert(x_con.size() == y_con.size());
    for(int i=0;i<x_con.size();i++)
    {
	assert(get<0>(x_con[i]) == get<0>(y_con[i]));
	auto& xmax = get<1>(x_con[i]);
	auto& xmin = get<2>(x_con[i]);

	auto& ymax = get<1>(y_con[i]);
	auto& ymin = get<2>(y_con[i]);

	if (xmax and ymin)
	    yboundaries[*xmax].second = std::min(*ymin, yboundaries[*xmax].second);
	if (xmin and ymax)
	    yboundaries[*xmin+1].first = std::max(*ymax+1, yboundaries[*xmin+1].first);
    }

    for(int i=1; i<=I; i++)
	yboundaries[i].first = std::max(yboundaries[i-1].first, yboundaries[i].first);

    for(int i=I-1; i>=0; i--)
	yboundaries[i].second = std::min(yboundaries[i+1].second, yboundaries[i].second);

    return yboundaries;
}

template<typename T>
optional<T> max(const optional<T>& x, const optional<T>& y)
{
    if (not x) return y;
    if (not y) return x;
    return std::max(*x,*y);
}

template<typename T>
optional<T> min(const optional<T>& x, const optional<T>& y)
{
    if (not x) return y;
    if (not y) return x;
    return std::min(*x,*y);
}



void check_constraints(const alignment_constraints& con_x, const alignment_constraints& con_y,
		       const pairwise_alignment_t& a_xy, const pair<matrix<int>,vector<int>>& con_matrix)
{
    auto& totals = con_matrix.second;

    assert(con_x.size() == con_y.size());
    auto max_y_le_x = get_max_y_le_x(a_xy);
    auto min_y_ge_x = get_min_y_ge_x(a_xy);

    bool fail = false;

    for(int i=0; i < con_x.size(); i++)
    {
	auto& xc = con_x[i];
	auto& yc = con_y[i];
	assert(get<0>(xc) == get<0>(yc));
	int id = get<0>(xc);

	auto ymax_x = lookup(max_y_le_x, get<1>(xc));
	auto ymin_x = lookup(min_y_ge_x, get<2>(xc));
	int xnum = get<3>(xc);

	auto ymax_y = get<1>(yc);
	auto ymin_y = get<2>(yc);
	int ynum = get<3>(yc);

	assert(xnum + ynum == totals[id]);

        // 3c. Check that the constraint is met on the X and Y sequences.
	if (ymax_x and ymin_y and not (*ymax_x < *ymin_y) )
	{
	    std::cerr<<"Constraint "<<id<<" failed: ymax_x ("<<*ymax_x<<") not less than ymin_y ("<<*ymin_y<<")\n";
	    fail = true;
	}
	if (ymax_y and ymin_x and not (*ymax_y < *ymin_x) )
	{
	    std::cerr<<"Constraint "<<id<<" failed: ymax_y ("<<*ymax_y<<") not less than ymin_x ("<<*ymin_x<<")\n";
	    fail = true;
	}
    }

    if (fail)
	throw myexception()<<"constraints failed!";
}

alignment_constraints merge_alignment_constraints(const alignment_constraints& con_x, const pairwise_alignment_t& a_xz,
						  const alignment_constraints& con_y, const pairwise_alignment_t& a_yz,
						  const pair<matrix<int>,vector<int>>& con_matrix)
{
    auto& totals = con_matrix.second;

    auto max_z_le_x = get_max_y_le_x(a_xz);
    auto max_z_le_y = get_max_y_le_x(a_yz);

    auto min_z_ge_x = get_min_y_ge_x(a_xz);
    auto min_z_ge_y = get_min_y_ge_x(a_yz);

    alignment_constraints con_z;
    con_z.reserve(con_x.size()+con_y.size());

    for(auto xi = con_x.begin(), yi = con_y.begin(); xi != con_x.end() or yi != con_y.end();)
    {
	auto x_id = (xi != con_x.end()) ? optional<int>(get<0>(*xi)) : {};
	auto y_id = (yi != con_y.end()) ? optional<int>(get<0>(*yi)) : {};
	int id = *min(x_id, y_id);

	bool have_x_con = (x_id == id);
	bool have_y_con = (y_id == id);

	assert(have_x_con or have_y_con);

	optional<int> zmax_x;
	optional<int> zmax_y;

	optional<int> zmin_x;
	optional<int> zmin_y;

	int xnum = 0;
	int ynum = 0;

        // 3a. Get the zmax(X-Delta) and zmax(X+Delta)
	if (have_x_con)
	{
	    zmax_x = lookup(max_z_le_x, get<1>(*xi));
	    zmin_x = lookup(min_z_ge_x, get<2>(*xi));
	    xnum = get<3>(*xi);
	    xi++;
	}

	// 3b. Get the zmax(X-Delta) and zmax(X+Delta)
	if (have_y_con)
	{
	    zmax_y = lookup(max_z_le_y, get<1>(*yi));
	    zmin_y = lookup(min_z_ge_y, get<2>(*yi));
	    ynum = get<3>(*yi);
	    yi++;
	}

	// 3c. Check that the constraint is met on the X and Y sequences.
	if (zmax_x and zmin_y and not (*zmax_x < *zmin_y) ) throw myexception()<<"X-D !>= Y+D constraints failed!";
	if (zmax_y and zmin_x and not (*zmax_y < *zmin_x) ) throw myexception()<<"Y-D !>= X+D constraints failed!";

	// max_{xy in (X U Y)-Delta} max {z <= xy}
	auto zmax = std::max(zmax_x, zmax_y);
	// min_{xy in (X U Y)+Delta} min {z >= xy}
	auto zmin = std::min(zmin_x, zmin_y);
	int znum = xnum + ynum;

	if (znum < totals[id])
	    con_z.push_back(alignment_constraint{id, zmax, zmin, znum});
    }
    return con_z;
}

//// --- The old constraints --- ///

string clean(const string& in) {
    string out;
    char c=' ';
    for(int i=0;i<in.size();i++)
	if (in[i] != ' ' or c != ' ') {
	    out += in[i];
	    c = in[i];
	}

    // strip (single) final ' '
    if (out.size() > 0 and out[out.size()-1] == ' ')
	out = out.substr(0,out.size()-1);
    return out;
}
    
matrix<int> load_alignment_constraint(const string& filename,SequenceTree& T) 
{
    matrix<int> constraint(0,T.n_leaves());

    if (filename.size()) {
	// Load constraint file
	checked_ifstream constraint_file(filename,"alignment-constraint file");

	// Map columns to species
	string line;
	portable_getline(constraint_file,line);
	vector<string> names = split(clean(line),' ');
	vector<int> mapping;
	try {
	    mapping = compute_mapping(names,T.get_leaf_labels());
	}
	catch (myexception& e) 
	{
	    myexception error;
	    error <<"Problem loading alignment constraints from file '" <<filename<<"':\n";

	    // complain about the names;
	    if (names.size() != T.n_leaves())
		error <<"Data set contains "<<T.n_leaves()<<" sequences but "
		    "alignment-constraint header has "<<names.size()<<" names.\n";

	    for(int i=0;i<names.size();i++) {
		if (not includes(T.get_leaf_labels(), names[i]))
		    error<<"'"<<names[i]<<"' found in header but not data set.\n";
	    }

	    for(int i=0;i<T.n_leaves();i++) {
		if (not includes(names,T.get_label(i)))
		    error<<"'"<<T.get_label(i)<<"' found in data set but not in header.\n";
	    }
	    throw error;
	}

	// Load constraints
	vector<vector<int> > constraints;

	// We start on line 1
	int line_no=0;
	while(portable_getline(constraint_file,line)) 
	{
	    line_no++;

	    // Check for comment marker -- stop before it.
	    int loc = line.find('#');
	    if (loc == -1)
		loc = line.length();

	    while (loc > 0 and line[loc-1] == ' ')
		loc--;

	    line = line.substr(0,loc);

	    if (not line.size()) continue;

	    // lex contraint line
	    vector<string> entries = split(clean(line),' ');
	    if (entries.size() != T.n_leaves())
		throw myexception()<<"constraint: line "<<line_no<<
		    " only has "<<entries.size()<<"/"<<T.n_leaves()<<" entries.";

	    // parse contraint line
	    int n_characters = 0;
	    vector<int> c_line(T.n_leaves());
	    for(int i=0;i<entries.size();i++) {
		if (entries[i] == "-")
		    c_line[mapping[i]] = alphabet::gap;
		else {
		    int index = convertTo<int>(entries[i]);

		    if (index < 0)
			throw myexception()<<"constraint: line "<<line_no<<
			    " has negative index '"<<index<<"' for species '"<<names[i]<<"' (entry "<<i+1<<").";

		    //FIXME - we should probably check that the index is less than the length of the sequence

		    c_line[mapping[i]] = index;

		    n_characters++;
		}
	    }

	    // Only add a constraint if we are "constraining" more than 1 character
	    if (n_characters >= 2)
		constraints.push_back(c_line);
	}

	// load constraints into matrix
	constraint.resize(constraints.size(),T.n_leaves());
	for(int i=0;i<constraint.size1();i++)
	    for(int j=0;j<constraint.size2();j++)
		constraint(i,j) = constraints[i][j];
    }

    return constraint;
}

bool constrained(const dynamic_bitset<>& group,const matrix<int>& constraint,int c) 
{
    bool present = false;
    for(int i=0;i<constraint.size2();i++)
	if (group[i] and constraint(c,i) != -1)
	    present = true;
    return present;
}

// This procedure bases the constraint columns ENTIRELY on the leaf sequence alignment!
// Therefore these constrained columns may be unalignable, depending on the internal node
//  states!
vector<int> constraint_columns(const matrix<int>& constraint,const alignment& A) 
{
    // determine which constraints are satisfied, and can be enforced
    vector<int> columns(constraint.size1(),-1);

    // get columns for each residue
    vector<vector<int> > column_indices = column_lookup(A);

    // for all constraints (i,*) != -1, check...
    for(int i=0;i<constraint.size1();i++) 
	for(int j=0;j<constraint.size2();j++) 
	    if (constraint(i,j) != -1) 
	    {
		int c = column_indices[j][constraint(i,j)];

		if (columns[i] == -1)
		    columns[i] = c;
		else if (columns[i] != c) {
		    columns[i] = -1;
		    break;
		}
	    }

    return columns;
}


// When the alignment is project onto 2 or 3 sequences, its columns are ordered 
// in a particular way so that only one path through the DP matrix corresponds to 
// each alignment.
// 
// seq1 is a list of columns that contain the x-ordinate sequence(s)
// seq2 is a list of columns that contain the y-coordinate sequence(s)
// seq12 is a list of columns that occur in either of the two sequences, and represents
//      the current path through the DP matrix.

// This routine moves a square at [x-D,x+D]*[y-D,y+D] along the points x,y in seq12 to
// find the leftmost and rightmost x-coordinates for each y.  As y increases, these
// two x-coordinates may not decrease.

// Question.  Is the (0,0) square actually at (1,1) in the matrix?
// Answer. Yes, but we are going to store ranges in the unadjusted (0,0) coordinates.

vector< pair<int,int> > get_x_ranges_for_band(int D, const vector<int>& seq1, const vector<int>& seq2, 
					      const vector<int>& seq12)
{
    // The DP matrix has size (W+1)*(H+1) and is [0,W]x[0,H]
    int W = seq1.size();
    int H = seq2.size();

    // we'll compute the first and last indices, instead of first and last+1
    vector< pair<int,int> > xboundaries(H+1, pair<int,int>(0,W));

    if (D<0) return xboundaries;

    // Determine xmin[y]
    for(int x=0,y=0,k=0;k<seq12.size();k++)
    {
	if (x<seq1.size() and seq1[x] == seq12[k])
	    x++;
	if (y<seq2.size() and seq2[y] == seq12[k])
	{
	    y++;

	    // Avoid setting an xmin not in [0,W]
	    if (x-D < 0) continue;

	    // If the top of the square is out of the DP matrix then we are done.
	    if (y+D > H) break;

	    // Set the xmax for row y+D
	    xboundaries[y+D].first = x-D;
	}
    }

    // Determine xmax[y]
    for(int x=W,y=H,k=seq12.size()-1;k>=0;k--)
    {
	if (x>0 and seq1[x-1] == seq12[k])
	    x--;
	if (y>0 and seq2[y-1] == seq12[k])
	{
	    y--;

	    // Avoid setting an xmin not in [0,W]
	    if (x+D > W) continue;

	    // If the top of the square is out of the DP matrix then we are done
	    if (y-D < 0) break;

	    // Set the xmax for row y-D
	    xboundaries[y-D].second = x+D;
	}
    }

    return xboundaries;
}

vector< pair<int,int> > get_y_ranges_for_band(int D, const vector<int>& seq1, const vector<int>& seq2, 
					      const vector<int>& seq12)
{
    return get_x_ranges_for_band(D, seq1, seq2, seq12);
}

// We need to make sure that the pinned column coordinates always increase.
// By considering constraints between seq1 and seq2 in the order of seq12 we can guarantee this,
//  or bail out if it is impossible.

vector< vector<int> > get_pins(const matrix<int>& constraint,const alignment& A,
			       const dynamic_bitset<>& group1,const dynamic_bitset<>& group2,
			       const vector<int>& seq1,const vector<int>& seq2)
{
    // determine which constraints are satisfied (not necessarily enforceable!)
    vector<int> satisfied = constraint_columns(constraint,A);

    // ignore columns in which all constrained residues are in either group1 or group2
    // we cannot enforce these constraints, and also cannot affect them
    for(int i=0;i<satisfied.size();i++) 
	if (not (constrained(group1,constraint,i) and constrained(group2,constraint,i)))
	    satisfied[i] = -1;

    vector< vector<int> > impossible;
    impossible.push_back(vector<int>(2,-1));

    // Mark and check each alignment column which is going to get pinned.
    vector<set<int>> x_constraints(seq1.size());
    vector<set<int>> y_constraints(seq2.size());
    for(int i=0;i<satisfied.size();i++) 
    {
	int column = satisfied[i];

	if (column != -1)
	{
	    auto x = find_index(seq1,column);
	    auto y = find_index(seq2,column);

	    // Even if the constraints for the leaf nodes are satisfied, we can't align
	    // to the relevant leaf characters THROUGH the relevant internal nodes, if the
	    // character is not present at the internal nodes that we have
	    // access to.  Therefore, no alignment that we choose can satisfy
	    // this constraint, so we must bail out.
	    if (not x or not y)
		return impossible;

	    x_constraints[*x].insert(i);
	    y_constraints[*y].insert(i);
	}
    }

    // Go through the pinned columns in seq12 order to guarantee that x and y always increase
    vector<vector<int> > pins(2);
    vector<int>& X = pins[0];
    vector<int>& Y = pins[1];

    /* TODO: Note that we cannot have pins like (x1,y1) (x1,y2)
       because we can only pin matches, and the second one
       would be a gap. */

    for(int x=0,y=0;;x++,y++)
    {
	for(;x<seq1.size() and x_constraints[x].empty();x++)
	    ;
	for(;y<seq2.size() and y_constraints[y].empty();y++)
	    ;

	if (x == seq1.size() and y == seq2.size()) break;

	if (x == seq1.size() or y == seq2.size()) return impossible;

	if (x_constraints[x] != y_constraints[y]) return impossible;

	assert(x >=0 and x < seq1.size());
	assert(y >=0 and y < seq2.size());

	X.push_back(x+1);
	Y.push_back(y+1);

	if (X.size() >= 2 and X[pins.size()-2] > X[pins.size()-1])
	    throw myexception()<<"X pins not always increasing!";
	if (Y.size() >= 2 and Y[pins.size()-2] > Y[pins.size()-1])
	    throw myexception()<<"X pins not always increasing!";
    }

    return pins;
}


dynamic_bitset<> constraint_satisfied(const matrix<int>& constraint,const alignment& A) 
{
    vector<int> columns = constraint_columns(constraint,A);

    dynamic_bitset<> satisfied(columns.size());
    for(int i=0;i<satisfied.size();i++)
	satisfied[i] = columns[i] != -1;

    return satisfied;
}

namespace {
    int sum(const dynamic_bitset<>& v) {
	int count = 0;
	for(int i=0;i<v.size();i++)
	    if (v[i]) count++;
	return count;
    }
}

void report_constraints(const dynamic_bitset<>& s1, const dynamic_bitset<>& s2, int p) 
{
    p++;
    assert(s1.size() == s2.size());

    if (not s1.size()) return;

    for(int i=0;i<s1.size();i++) {
	if (s1[i] and not s2[i])
	    throw myexception()<<"Partition "<<p<<": constraint "<<i<<" went from satisfied -> unsatisfied!";
	if (s2[i] and not s1[i])
	    std::cout<<"Partition "<<p<<": constraint "<<i<<" satisfied."<<std::endl;
    }

    if (sum(s1) != sum(s2)) {
	std::cout<<"Partition "<<p<<": "<<sum(s2)<<"/"<<s2.size()<<" constraints satisfied.\n";

	if (sum(s2) == s2.size())
	    std::cout<<"Partition "<<p<<": All constraints satisfied!"<<std::endl;
    }
}

bool any_branches_constrained(const vector<int>& branches,const SequenceTree& T,const SequenceTree& TC, const vector<int>& AC)
{
    if (AC.size() == 0)
	return false;

    vector<int> c_branches = compose(AC,extends_map(T,TC));

    for(int i=0;i<branches.size();i++)
	if (includes(c_branches,branches[i]))
	    return true;

    return false;
}

vector< pair<int,int> > get_yboundaries_from_pins(int I, int J, const vector< vector<int> >& pins)
{
    vector< pair<int,int> > yboundaries(I, pair<int,int>(0,J-1));

    const vector<int>& x = pins[0];
    const vector<int>& y = pins[1];

    if (x.size() != 0)
    {
	for(int i=0;i<x[0];i++)
	    yboundaries[i] = pair<int,int>(0, y[0]-1);

	for(int k=0;k+1<(int)x.size();k++)
	    for(int i=x[k];i<x[k+1];i++)
		yboundaries[i] = pair<int,int>(y[k], y[k+1]-1);

	for(int i=x.back();i<I;i++)
	    yboundaries[i] = pair<int,int>(y.back(), J-1);
    }

    return yboundaries;
}

vector< pair<int,int> > boundaries_intersection(const vector< pair<int,int> >& boundaries1,const vector< pair<int,int> >& boundaries2)
{
    assert(boundaries1.size());

    assert(boundaries1.size() == boundaries2.size());

    assert(boundaries1[0].first == 0);
    assert(boundaries2[0].first == 0);

//    int L1 = boundaries1.size()-1;

    assert(boundaries1.back().second == boundaries2.back().second);
//    int L2 = boundaries1.back().second;

    vector< pair<int,int> > boundaries3 = boundaries1;

    for(int i=0; i<boundaries3.size();i++)
    {
	boundaries3[i].first = std::max(boundaries3[i].first, boundaries2[i].first);
	boundaries3[i].second = std::min(boundaries3[i].second, boundaries2[i].second);
	assert(boundaries3[i].second >= boundaries3[i].first);
    }

    return boundaries3;
}
