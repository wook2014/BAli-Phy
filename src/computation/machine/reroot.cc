#include <iostream>
#include "graph_register.H"
#include <algorithm>
#include "util/range.H"
#include "mapping.H"

using std::string;
using std::vector;
using std::pair;

using std::cerr;
using std::endl;

long total_steps_pivoted = 0;
long total_results_pivoted = 0;
long total_reroot = 0;
long total_reroot_one = 0;
long total_invalidate = 0;
long total_steps_invalidated = 0;
long total_results_invalidated = 0;
long total_steps_scanned = 0;
long total_results_scanned = 0;

void reg_heap::reroot_at_context(int c)
{
    int old_root = root_token;

    // 1. Bail if we are already at the root.
    int t = token_for_context(c);
    if (is_root_token(t)) return;

    total_reroot++;

    // 2. Get the tokens on the path to the root.
    boost::container::small_vector<int,10> path;
    path.push_back(token_for_context(c));
    while(true)
    {
        int parent = tokens[path.back()].parent;
        if (parent != -1)
            path.push_back(parent);
        else
            break;
    }

    // 3. Get the tokens on the path to the root.
    for(int i=int(path.size())-2; i>=0; i--)
        reroot_at(path[i]);

    // 4. Clean up old root token if it became an unused tip
    int t2 = release_unreferenced_tips(old_root);

    // 5. Remove sequences of knuckles - only remove a knuckle if its child was part of the original path
    for(; t2 != root_token;)
        t2 = release_knuckle_tokens(t2);
}

void reg_heap::reroot_at(int t)
{
    assert(not is_root_token(t) and is_root_token(tokens[t].parent));

#ifdef DEBUG_MACHINE
    check_used_regs();
#endif

    // 1. If this context isn't a direct child of the root, then make it one
    if (not is_root_token(parent_token(t)))
        reroot_at(parent_token(t));

    // re-rooting to the parent context shouldn't release its token.
    int parent = parent_token(t);
    assert(is_root_token(parent));

    // 2. Unshare regs
    unshare_regs(t);

    // 3. Change the relative mappings
    total_steps_pivoted += tokens[t].delta_step().size();
    total_results_pivoted += tokens[t].delta_result().size();

    pivot_mapping(prog_steps, tokens[t].vm_step);
    std::swap(tokens[parent].vm_step, tokens[t].vm_step);
    pivot_mapping(prog_results, tokens[t].vm_result);
    std::swap(tokens[parent].vm_result, tokens[t].vm_result);

    pivot_mapping(prog_unforced_step, tokens[t].vm_unforced_step);
    std::swap(tokens[parent].vm_unforced_step, tokens[t].vm_unforced_step);
    pivot_mapping(prog_unforced_result, tokens[t].vm_unforced_result);
    std::swap(tokens[parent].vm_unforced_result, tokens[t].vm_unforced_result);

    // 4. Alter the inheritance tree
    tokens[parent].parent = t;
    int index = remove_element(tokens[parent].children, t);
    assert(index != -1);

    tokens[t].parent = -1;
    tokens[t].children.push_back(parent);

    root_token = t;
    assert(is_root_token(t));

    // 5. Remove probabilities for invalidated regs from the current probability

    for(auto& reroot_handler: reroot_handlers)
        reroot_handler(parent);

    total_reroot_one++;
  
    assert(tokens[parent].version == tokens[t].version);

    for(int t2: tokens[t].children)
        assert(tokens[t2].version <= tokens[t].version);

    assert(is_root_token(t));
}


/*
 * In the current framework, regs may be incorrectly shared, if they are not overridden in the child and should be.
 * However, if a reg is overridden in the child, then its result must be correct.
 * Therefore before pivoting a child of the root into the root, we just need to unshare steps and results that should not be shared.
 *
 * Consider a child of the root.
 *
 * - Some STEPS   in the root may be incorrectly shared into the child.
 *   This happens if the root STEP    uses a  RESULT that is overridden in the child, but the step   is shared into the child.
 *
 * - Some RESULTS in the root may be incorrectly shared into the child.
 *   This happens if the child RESULT calls a RESULT that is overridden in the child, but the result is shared into the child.
 *   The result is also incorrectly shared if the corresponding step is incorrectly shared.
 *
 * If a step is unshared, then its result must also be unshared.  Therefore, if we want to walk a list of unshared things that
 * we wish to consider processessing at a later time, we can just want the list of unshared results.
 *
 * Now, if we unshare all regs that are created in the root but overridden in the child,
 * then the child won't inherit any values from the root that it can't access.
 * This might help to ensure that when we delete a token, we destroy all of the objects that it created.
 * Currently we can't destroy created regs at the time of token destruction, because their steps might have floated down to the root.
 *
 * How do we add to this loop an unsharing of result AND steps for regs that were created by steps?
 * It seems like we could, in theory walk all the steps that we unshare after each round, and invalidate their steps and results,
 *  and then restart the inner loop to invalidate downstream steps and results.
 * result <-- called_by -- result
 * result <-- used_by  --- (step,result)
 *                         step <--- created_by --- reg <---located-at-- (step,result)
 */

void reg_heap::unshare_regs(int t)
{
    // parent_token(t) should be the root.
    assert(is_root_token(parent_token(t)));
    assert(tokens[root_token].version >= tokens[t].version);

    if (tokens[root_token].version <= tokens[t].version) return;

#if DEBUG_MACHINE >= 2
    check_used_regs();
#endif

    total_invalidate++;

    constexpr int result_bit = 0;
    constexpr int step_bit = 1;
    constexpr int unforced_result_bit = 2;
    constexpr int unforced_step_bit = 3;
  
    auto& vm_result = tokens[t].vm_result;
    auto& vm_step = tokens[t].vm_step;
    auto& vm_unforced_step = tokens[t].vm_unforced_step;
    auto& vm_unforced_result = tokens[t].vm_unforced_result;

    // find all regs in t that are not shared from the root
    const auto& delta_result = vm_result.delta();
    const auto& delta_step = vm_step.delta();
    const auto& delta_unforced_step = vm_unforced_step.delta();
    const auto& delta_unforced_result = vm_unforced_result.delta();

    int n_delta_result0 = delta_result.size();
    int n_delta_step0 = delta_step.size();

    auto unshare_unforced_step = [&](int r)
			    {
				if (not prog_temp[r].test(unforced_step_bit))
				{
				    prog_temp[r].set(unforced_step_bit);
				    vm_unforced_step.add_value(r, unforced_index);
				}
			    };

    auto unshare_unforced_result = [&](int r)
			    {
				if (not prog_temp[r].test(unforced_result_bit))
				{
				    prog_temp[r].set(unforced_result_bit);
				    vm_unforced_result.add_value(r, unforced_index);
				}
			    };

    auto unshare_result = [&](int r)
                              {
                                  // This result is already unshared
				  if (prog_temp[r].test(result_bit)) return;

				  unshare_unforced_result(r);

				  prog_temp[r].set(result_bit);
				  vm_result.add_value(r, non_computed_index);
                              };

    auto unshare_step = [&](int r)
                            {
                                // This step is already unshared
				if (prog_temp[r].test(step_bit)) return;

                                unshare_result(r);
				unshare_unforced_step(r);

				prog_temp[r].set(step_bit);
                                vm_step.add_value(r, non_computed_index);
                            };

    // All the regs with delta_result set have results invalidated in t
    for(const auto& [r,unforced]: delta_unforced_result)
	prog_temp[r].set(unforced_result_bit);

    // All the regs with delta_result set have results invalidated in t
    for(const auto& [r,result]: delta_result)
    {
        prog_temp[r].set(result_bit);
	prog_temp[r].set(result_bit);
	assert(prog_temp[r].test(result_bit));
	assert(prog_temp[r].test(unforced_result_bit));
    }

    for(const auto& [r,unforced]: delta_unforced_step)
	prog_temp[r].set(unforced_step_bit);

    // All the regs with delta_step set have steps (and results) invalidated in t
    for(const auto& [r,step]: delta_step)
    {
	prog_temp[r].set(step_bit);
	assert(prog_temp[r].test(result_bit));
	assert(prog_temp[r].test(step_bit));
	assert(prog_temp[r].test(unforced_result_bit));
	assert(prog_temp[r].test(unforced_step_bit));
    }

#ifndef NDEBUG
    for(auto [_,s]: delta_step)
    {
        if (s < 0) continue;

        const auto& Step = steps[s];

        // Any results or steps in the delta should already have their regs unshared.
        for(int r2: Step.created_regs)
        {
            auto t = regs.access(r2).type;
            if (t == reg::type_t::changeable or t == reg::type_t::unknown)
            {
                assert(prog_temp[r2].test(result_bit));
                assert(prog_temp[r2].test(step_bit));
	        assert(prog_temp[r2].test(unforced_result_bit));
	        assert(prog_temp[r2].test(unforced_step_bit));
            }
        }
    }
#endif
    int i =0; // (FIXME?) We have to rescan all the existing steps and results because there might be new EDGES to them that have been added.

    // Scan regs with different result in t that are used/called by root steps/results
    for(;i<delta_result.size();i++)
        if (auto [r,_] = delta_result[i]; has_result(r))
        {
            const auto& Result = result_for_reg(r);

            // Look at results that call the root's result (that is overridden in t)
            for(int res2: Result.called_by)
                if (int r2 = results[res2].source_reg; prog_results[r2] == res2)
                    unshare_result(r2);

            // Look at step that use the root's result (that is overridden in t)
            for(auto& [s2,_]: Result.used_by)
                if (int r2 = steps[s2].source_reg; prog_steps[r2] == s2)
                    unshare_step(r2);

	    // Look at step that use the root's result (that is overridden in t)
	    for(auto& [s2,index]: Result.forced_by)
	    {
		int r2 = steps[s2].source_reg;

		// The root program's step at r2 is s2, which uses the root program's result at r
		if (prog_steps[r2] == s2)
		    unshare_unforced_step(r2);
	    }
	}

    // LOGIC: Marking something unforced will never give it an invalid result.
    //        Therefore, this logic need not go into the former loop.
    int k=0,l=0;
    while(k < delta_unforced_result.size() or l < delta_unforced_step.size())
    {
	// Scan regs with different result in t that are used/called by root steps/results
	for(;k<delta_unforced_result.size();k++)
	{
	    int r = delta_unforced_result[k].first;

	    if (prog_temp[r].test(result_bit) or prog_temp[r].test(step_bit)) continue;

	    if (not has_result(r)) continue;

	    const auto& Result = result_for_reg(r);

	    // Look at results that call the root's result (that is overridden in t)
	    for(int res2: Result.called_by)
	    {
		int r2 = results[res2].source_reg;

		// The root program's result at r2 is res2, which calls the root program's result at r
		if (prog_results[r2] == res2)
		    unshare_unforced_result(r2);
	    }

	    // Look at step that use the root's result (that is overridden in t)
	    for(auto& [s2,index]: Result.used_by)
	    {
		int r2 = steps[s2].source_reg;

		// The root program's step at r2 is s2, which uses the root program's result at r
		if (prog_steps[r2] == s2)
		    unshare_unforced_step(r2);
	    }

	    // Look at steps that force the root's result (that is overridden in t)
	    for(auto& [s2,index]: Result.forced_by)
	    {
		int r2 = steps[s2].source_reg;

		// The root program's step at r2 is s2, which forces the root program's result at r
		if (prog_steps[r2] == s2)
		    unshare_unforced_step(r2);
	    }
	}

	// Scan regs with different result in t that are used/called by root steps/results
	for(;l<delta_unforced_step.size();l++)
	{
	    int r = delta_unforced_step[l].first;

	    if (prog_temp[r].test(result_bit) or prog_temp[r].test(step_bit)) continue;

	    if (not has_result(r)) continue;

	    const auto& Result = result_for_reg(r);

	    // Look at results that call the root's result (that is overridden in t)
	    for(int res2: Result.called_by)
	    {
		const auto& Result2 = results[res2];
		int r2 = Result2.source_reg;

		// The root program's result at r2 is res2, which calls the root program's result at r
		if (prog_results[r2] == res2)
		    unshare_unforced_result(r2);
	    }

	    // Look at step that use the root's result (that is overridden in t)
	    for(auto& [s2,index]: Result.used_by)
	    {
		int r2 = steps[s2].source_reg;

		// The root program's step at r2 is s2, which uses the root program's result at r
		if (prog_steps[r2] == s2)
		    unshare_unforced_step(r2);
	    }

	    // Look at steps that force the root's result (that is overridden in t)
	    for(auto& [s2,index]: Result.forced_by)
	    {
		int r2 = steps[s2].source_reg;

		// The root program's step at r2 is s2, which uses the root program's result at r
		if (prog_steps[r2] == s2)
		    unshare_unforced_step(r2);
	    }
	}
    }


//  int j = delta_step.size();
    int j=0; // FIXME if the existing steps don't share any created regs, then we don't have to scan them.
             // FIXME: while the overriding steps in the child should have their created regs unshared, the overridden steps in the root need not!
             //        this means that we need to scan all overridden steps each time :-(

    // Also unshare any results and steps that are for regs created in the root context.
    // LOGIC: Any reg that uses or call a created reg must either
    //          (i) be another created reg, or
    //          (ii) access the created reg through a chain of use or call edges to the step that created the reg.
    //        In the former case, this loop handles them.  In the later case, they should be invalid.
    for(;j<delta_step.size();j++)
        if (auto [r,_] = delta_step[j]; has_step(r))
            for(int r2: step_for_reg(r).created_regs)
            {
                auto t = regs.access(r2).type;
                if (t == reg::type_t::changeable or t == reg::type_t::unknown)
                    unshare_step(r2);
            }

#ifndef NDEBUG
    for(auto [_,s]: delta_step)
    {
        if (s < 0) continue;

        const auto& Step = steps[s];

        // Any results or steps in the delta should already have their regs unshared.
        for(int r2: Step.created_regs)
        {
            auto t = regs.access(r2).type;
            if (t == reg::type_t::changeable or t == reg::type_t::unknown)
            {
                assert(prog_temp[r2].test(result_bit));
                assert(prog_temp[r2].test(step_bit));
            }
        }
    }
#endif

    // Erase the marks that we made on prog_temp.
    for(const auto& p: delta_unforced_result)
    {
	int r = p.first;
	prog_temp[r].reset(result_bit);
	prog_temp[r].reset(step_bit);
	prog_temp[r].reset(unforced_result_bit);
	prog_temp[r].reset(unforced_step_bit);
    }

    total_results_invalidated += (delta_result.size() - n_delta_result0);
    total_steps_invalidated += (delta_step.size() - n_delta_step0);

    total_results_scanned += delta_result.size();
    total_steps_scanned += delta_step.size();

    tokens[t].version = tokens[root_token].version;
  
#if DEBUG_MACHINE >= 2
    check_used_regs();
#endif
}
