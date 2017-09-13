note
	description: "Summary description for {FUN}."
	author: "Jackie Wang"
	date: "$Date$"
	revision: "$Revision$"

class
	FUN[G -> attached ANY, H -> attached ANY]
inherit
	ITERABLE[PAIR[G, H]]
		redefine
			is_equal, out
		end
	DEBUG_OUTPUT
		undefine
			is_equal, out
		redefine
			debug_output
		end

create
	make_empty,
	make_from_array

feature -- Constructors

	make_empty
			-- Initialize an empty function
		do
			create dom.make (0)
			create ran.make (0)
		ensure
			# Current = 0
			is_empty
		end

	make_from_array (a: ARRAY[TUPLE[fst: G; snd: H]])
			-- Initialize a function from array 'a'.
		require
			no_duplicates:
				across a.lower |..| a.upper as i all
					across a.lower |..| a.upper as j all
						a[i.item] ~ a[j.item] IMPLIES i.item = j.item
					end
				end
		do
			make_empty
			across
				a as c
			loop
				dom.extend (c.item.fst)
				ran.extend (c.item.snd)
			end
		ensure
			consistent_counts:
				# Current = a.count
		end

feature {NONE} -- Implementation

	dom : ARRAYED_LIST[G]
	ran : ARRAYED_LIST[H]

feature -- Iterator

	new_cursor: ITERATION_CURSOR[PAIR[G, H]]
		local
			pairs: LINKED_LIST[PAIR[G, H]]
			pair: PAIR[G, H]
			i: INTEGER
		do
			create pairs.make
			from
				i := dom.lower
			until
				i > dom.upper
			loop
				create pair.make (dom[i], ran[i])
				pairs.extend (pair)
				i := i + 1
			end
			Result := pairs.new_cursor
		end

feature -- Set Commands

	extend (p: PAIR[G, H])
			-- Extend current function with mapping 'g |-> h'
		require
			not domain.has (p.first)
		do
			dom.extend (p.first)
			ran.extend (p.second)
		ensure
			old Current.deep_twin ~ Current - p
		end

	union (other: like Current)
			-- Extend current function with pairs in 'other'
		require
			(domain |/\| other.domain).is_empty
		local
			p: PAIR[G, H]
		do
			across
				other as c
			loop
				create p.make (c.item.first, c.item.second)
				extend (p)
			end
		ensure
			old Current.deep_twin |<: Current
			other |<: Current
			definition:
				hold_count (
					agent in_either_fun (?, old Current.deep_twin, other)) = count
		end

	subtract (p: PAIR[G, H])
			-- Subtract the mapping 'g |-> h' from current function.
		do
			from
				dom.start
				ran.start
			until
				dom.after
			loop
				if 			 dom.item ~ p.first
					and then ran.item ~ p.second
				then
					dom.remove
					ran.remove
				else
					dom.forth
					ran.forth
				end
			end
		ensure
			case_of_subtraction:
				(old Current.deep_twin).has (p) implies
					old Current.deep_twin ~ Current + p
			case_of_no_subtraction:
				not (old Current.deep_twin).has (p) implies
					old Current.deep_twin ~ Current
		end

	difference (other: like Current)
			-- Subtract all mappings in 'other' from current function.
		do
			across
				other as c
			loop
				subtract (create {PAIR[G, H]}.make (
					c.item.first, c.item.second))
			end
		ensure
			definition:
				old Current.deep_twin ~
					Current |\/| (old Current.deep_twin |/\| other)
		end

	intersect (other: like Current)
			-- Intersect with mappings in 'other'
		local
			p: PAIR[G, H]
		do
			from
				dom.start
				ran.start
			until
				dom.after
			loop
				create p.make (dom.item, ran.item)
				if not other.has (p) then
					dom.remove
					ran.remove
				else
					dom.forth
					ran.forth
				end
			end
		ensure
			Current |<: old Current.deep_twin
			Current |<: other
			definition:
				hold_count (agent in_both_fun (?, old Current.deep_twin, other)) = count
		end


feature -- Relation Commands

	domain_restrict (ds: SET[G])
			-- Keep all pairs whose first values are members of 'ds'.
		do
			domain_subtract (domain |\ ds)
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_ds_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).domain ~ (old Current.deep_twin.domain |\ ds)
		end

	domain_restrict_by (g: G)
			-- Keep pairs whose first values are 'd'.
		do
			domain_subtract (domain - g)
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_g_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).domain ~ (old Current.deep_twin.domain |\ singleton_g (g))
		end

	range_restrict (rs: SET[H])
			-- Keep all pairs whose second values are members of 'rs'.
		do
			range_subtract (range |\ rs)
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_rs_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).range ~ (old Current.deep_twin.range |\ rs)
		end

	range_restrict_by (h: H)
			-- Keep all pairs whose second values are 'h'.
		do
			range_subtract (range |\ singleton_h (h))
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_h_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).range ~ (old Current.deep_twin.range |\ singleton_h (h))
		end

	domain_subtract (ds: SET[G])
			-- Subtract all pairs whose first values are members of 'ds'.
		do
			from
				dom.start
				ran.start
			until
				dom.after
			loop
				if ds.has (dom.item) then
					dom.remove
					ran.remove
				else
					dom.forth
					ran.forth
				end
			end
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_ds_in_new_fun:
				-- in case 'ds' contains items not in the domain
				( (old Current.deep_twin) |\ (Current) ).domain ~
					ds.comprehension (agent in_domain (?, (old Current.deep_twin).domain))
		end

	domain_subtract_by (g: G)
			-- Subtract the pair whose first value is 'd'
		do
			domain_subtract (create {SET[G]}.make_from_array (<<g>>))
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_g_in_new_fun:
				-- in case 'g' is not in the domain
				( (old Current.deep_twin) |\ (Current) ).domain ~
					singleton_g (g).comprehension (agent in_domain (?, (old Current.deep_twin).domain))
		end

	range_subtract (rs: SET[H])
			-- Subtract all pairs whose second values are members of 'rs'.
		local
			h: H
		do
			from
				dom.start
				ran.start
			until
				dom.after
			loop
				h := ran.item
				if rs.has (h) then
					dom.remove
					ran.remove
				else
					dom.forth
					ran.forth
				end
			end
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_rs_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).range ~
					-- in case 'rs' contains items not in the range
					rs.comprehension (agent in_range (?, (old Current.deep_twin).range))
		end

	range_subtract_by (h: H)
			-- Subtract pairs whose second values are 'h'.
		do
			range_subtract (create {SET[H]}.make_from_array (<<h>>))
		ensure
			new_fun_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_h_in_new_fun:
				( (old Current.deep_twin) |\ (Current) ).range ~
					-- in case 'h' is not in the range
					singleton_h (h).comprehension (agent in_range (?, (old Current.deep_twin).range))
		end

	override (r: like Current)
			-- Update current function such that it aggres on 'r'.
		do
			domain_subtract (r.domain)
			union (r)
		ensure
			Current ~ ( (old Current.deep_twin |<< r.domain) |\/| r )
		end

	override_by (t: TUPLE[g: G; h: H])
			-- Update current function such that it aggres on 'g |-> h'.
		do
			domain_subtract_by (t.g)
			extend (create {PAIR[G, H]}.make (t.g, t.h))
		ensure
			Current ~ ( (old Current.deep_twin @<< t.g) |\/| singleton_gh (t) )
		end

	put(h: H; g: G)
		require
			domain.has(g)
		do
			override_by ([g,h])
		ensure
			Current[g] ~ h
		end

feature -- Set Queries

	count alias "#": INTEGER
			-- How many pair are in current function?
		do
			Result := dom.count
		ensure
			Result = # domain
		end

	is_empty: BOOLEAN
			-- Does current function contain no pairs?
		do
			Result := count = 0
		ensure
			Result = (# Current = 0)
		end

	has (p: PAIR[G, H]): BOOLEAN
			-- Does current contain the mapping 'g -> h'?
		do
			Result := domain.has (p.first)
				and then Current[p.first] ~ p.second
		end

	is_subset_of alias "|<:" (other: like Current): BOOLEAN
			-- Is current function a subset of 'other'?
		local
			i : INTEGER
			p : PAIR[G, H]
		do
			from
				Result := TRUE
				i := dom.lower
			until
				NOT Result OR ELSE i > dom.upper
			loop
				create p.make (dom [i], ran [i])
				Result := other.has (p)
				i := i + 1
			end
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			Result =
				across
					Current as cur
				all
					other.has (create {PAIR[G, H]}.make (cur.item.first, cur.item.second))
				end
		end

	extended alias "+" (p: PAIR[G, H]): like Current
			-- Return a new function representing the addtion of current and 'g'.
		require
			not domain.has (p.first)
		do
			create Result.make_empty
			Result.set_imp (dom.twin, ran.twin)
			Result.extend (p)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			extension:
				Current ~ Result - p
		end

	unioned alias "|\/|" (other: like Current): like Current
			-- Return a new function representing the union of current and 'other'.
		require
			(domain |/\| other.domain).is_empty
		do
			create Result.make_empty
			Result.set_imp (dom.twin, ran.twin)
			Result.union (other)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			items_from_either_set:
				across
					Result as it
				all
						Current.has (create {PAIR[G, H]}.make (it.item.first, it.item.second))
					OR 	other.has (create {PAIR[G, H]}.make (it.item.first, it.item.second))
				end
		end

	subtracted alias "-" (p: PAIR[G, H]): like Current
			-- Return a new function representing the difference between Current and 't.g |-> t.h'.
		do
			create Result.make_empty
			Result.set_imp (dom.twin, ran.twin)
			Result.subtract (p)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			case_of_subtraction:
				has (p) implies Current ~ Result + p
			case_of_no_subtraction:
				not has (p) implies Current ~ Result
		end

	differenced alias "|\" (other: like Current): like Current
			-- Return a new function representing the difference between Current and 'other'.
		local
			p: PAIR[G, H]
		do
			create Result.make_empty

			across
				Current as src
			loop
				create p.make (src.item.first, src.item.second)
				if not other.has (p) then
					Result.extend (p)
				end
			end
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			definition:
				Current ~ Result |\/| (Current |/\| other)
		end

	intersected alias "|/\|" (other: like Current): like Current
			-- Return a new fun representing the intersection of current and 'other'.
		local
			p: PAIR[G, H]
		do
			create Result.make_empty

			across
				other as it
			loop
				create p.make (it.item.first, it.item.second)
				if has (p) then
					Result.extend (p)
				end
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			items_from_both_set:
				across
					Result as it
				all
						Current.has (create {PAIR[G, H]}.make (it.item.first, it.item.second))
					AND other.has (create {PAIR[G, H]}.make (it.item.first, it.item.second))
				end
		end

feature -- Relation Status Queries

	is_function: BOOLEAN
			-- Is Current a function?
		local
			i, j: INTEGER
		do
			from
				Result := TRUE
				i := dom.lower
			until
				NOT Result OR ELSE i > dom.upper
			loop
				from
					j := dom.lower
				until
					NOT Result OR ELSE j > dom.upper
				loop
					if i /= j and then dom[i] ~ dom[j] then
						Result := FALSE
					end
					j := j + 1
				end
				i := i + 1
			end
		end

	is_injection: BOOLEAN
			-- Is Current an injective function?
		local
			i, j: INTEGER
		do
			from
				Result := TRUE
				i := ran.lower
			until
				NOT Result OR ELSE i > ran.upper
			loop
				from
					j := ran.lower
				until
					NOT Result OR ELSE j > ran.upper
				loop
					if i /= j and then ran[i] ~ ran[j] then
						Result := FALSE
					end
					j := j + 1
				end
				i := i + 1
			end
		end

	domain: SET[G]
			-- Return the domain set of function.
		do
			create Result.make_empty
			across Current as c loop
				Result.extend (c.item.first)
			end
		end

	range: SET[H]
			-- Return the range set of function.
		do
			create Result.make_empty
			across Current as c loop
				Result.extend (c.item.second)
			end
		end

feature -- Relation Operation Queries

	item alias "[]" (g: G): H assign put
		require
			domain.has (g)
		local
			found: BOOLEAN
		do
			Result := ran.first
			from
				dom.start
				ran.start
			until
				found OR ELSE dom.after
			loop
				if dom.item ~ g then
					Result := ran.item
					found := TRUE
				else
					dom.forth
					ran.forth
				end
			end
		ensure then
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			result_in_range:
				range.has (Result)
		end

	domain_restricted alias "|<" (ds: SET[G]): like Current
			-- Return a copy of current function with
			-- all pairs whose first values are members of 'ds' kept.
		do
			Result := Current.deep_twin
			Result.domain_restrict (ds)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			only_ds_in_new_fun:
				( Current |\ Result ).domain ~ (domain |\ ds)
		end

	domain_restricted_by alias "@<" (g: G): like Current
			-- Return a copy of current funcion with
			-- all pairs whose first values are 'g' kept.
		do
			Result := Current.deep_twin
			Result.domain_restrict_by (g)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			only_g_in_new_fun:
				( Current |\ Result ).domain ~ (domain |\ singleton_g (g))
		end

	range_restricted alias "|>" (rs: SET[H]): like Current
			-- Return a copy of current function with
			-- all pairs whose second values are members of 'rs' kept.
		do
			Result := Current.deep_twin
			Result.range_restrict (rs)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			only_rs_in_new_fun:
				( Current |\ Result ).range ~ (range |\ rs)
		end

	range_restricted_by alias "@>" (h: H): like Current
			-- Return a copy of current function with
			-- all pairs whose second values are 'h' kept.
		do
			Result := Current.deep_twin
			Result.range_restrict_by (h)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			only_h_in_new_fun:
				( Current |\ Result ).range ~ (range |\ singleton_h (h))
		end

	domain_subtracted alias "|<<" (ds: SET[G]): like Current
			-- Return a new copy of current function with
			-- all pairs whose first values are members of 'ds' subtracted.
		do
			Result := Current.deep_twin
			Result.domain_subtract (ds)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			no_ds_in_new_fun:
				( Current |\ Result ).domain ~
					-- in case 'ds' contains items not in the domain
					ds.comprehension (agent in_domain (?, domain))
		end

	domain_subtracted_by alias "@<<" (g: G): like Current
			-- Return a new copy of current function with
			-- all pairs whose first values 'g' subtracted.
		do
			Result := Current.deep_twin
			Result.domain_subtract_by (g)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			no_ds_in_new_fun:
				( Current |\ Result ).domain ~
					-- in case 'g' is not in the domain
					singleton_g (g).comprehension (agent in_domain (?, domain))
		end

	range_subtracted alias "|>>" (rs: SET[H]): like Current
			-- Return a new copy of current function with
			-- all pairs whose second values are members of 'rs' subtracted.
		do
			Result := Current.deep_twin
			Result.range_subtract (rs)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			no_rs_in_new_fun:
				( Current |\ Result ).range ~
					-- in case 'rs' contains items not in the range
					rs.comprehension (agent in_range (?, range))
		end

	range_subtracted_by alias "@>>" (h: H): like Current
			-- Return a new copy of current function with
			-- all pairs whose second values are 'h' subtracted.
		do
			Result := Current.deep_twin
			Result.range_subtract_by (h)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			new_fun_is_a_subset:
				Result |<: Current
			no_rs_in_new_fun:
				( Current |\ Result ).range ~
					-- in case 'h' is not in the range
					singleton_h (h).comprehension (agent in_range (?, range))
		end

	overriden alias "|<+" (r: like Current): like Current
			-- Return a copy of current function that agrres on 'r'.
		do
			Result := Current.deep_twin
			Result.override (r)
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			Result ~ ( (Current |<< r.domain) |\/| r )
		end

	overriden_by alias "@<+" (t: TUPLE[g: G; h: H]): like Current
			-- Return a copy of current function that agrres on 'g |-> h'.
		do
			Result := Current.deep_twin
			Result.override_by (t.g, t.h)
			t.compare_objects
		ensure
			current_fun_unchanged:
				Current ~ old Current.deep_twin
			Result ~ ( (Current @<< t.g) |\/| singleton_gh (t.g, t.h) )
		end

feature -- Quantifiers

   hold_count (exp: PREDICATE [PAIR[G, H]]): INTEGER
			-- How many items satisfying `exp' are in `Current'?
		local
			i: INTEGER
			p: PAIR[G, H]
		do
			across
				Current as c
			loop
				create p.make (c.item.first, c.item.second)
				if exp.item ([p]) then
					Result := Result + 1
				end
				i := i + 1
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			maximum_result: Result <= count
		end

	comprehension alias "|" (exp: PREDICATE [PAIR[G, H]]): like Current
			-- Largest subset of the current fun whose elements satisfy `exp'
		local
			p: PAIR[G, H]
		do
			create Result.make_empty
			across
				Current as c
			loop
				create p.make (c.item.first, c.item.second)
				if exp.item ([p]) then
					Result.extend (p)
				end
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			is_subset: Result |<: Current
			all_satisfying_exp: Result.hold_count (exp) = # Result
			consistent_satisfying_items: Current.hold_count (exp) = # Result
		end

feature -- Conversion

	as_set: SET[PAIR[G, H]]
			-- Return current function as a set of pairs
		local
			pair: PAIR[G, H]
		do
			create Result.make_empty
			across
				Current as c
			loop
				create pair.make (c.item.first, c.item.second)
				Result.extend (pair)
			end
		end

	as_array: ARRAY[PAIR[G, H]]
		local
			pair: PAIR[G, H]
		do
			create Result.make_empty
			across
				Current as c
			loop
				create pair.make (c.item.first, c.item.second)
				Result.force (pair,	 Result.upper + 1)
			end
		end

feature -- Equality

	is_equal (other: like Current): BOOLEAN
			-- Is current function equal to 'other'?
		do
			Result := as_set.is_equal (other.as_set)
		end

feature {FUN} -- Auxiliary functions

	set_imp (new_dom: like dom; new_ran: like ran)
		do
			dom := new_dom
			ran := new_ran
			dom.compare_objects
			ran.compare_objects
		end

	singleton_g (g: G): SET[G]
		do
			create Result.make_from_array (<<g>>)
		ensure
			# Result = 1
			Result.has (g)
		end

	singleton_h (h: H): SET[H]
		do
			create Result.make_from_array (<<h>>)
		ensure
			# Result = 1
			Result.has (h)
		end

	singleton_gh (t: TUPLE[g: G; h: H]): FUN[G, H]
		do
			create Result.make_from_array (<<t>>)
		ensure
			# Result = 1
		end

	in_domain (g: G; ds: SET[G]): BOOLEAN
		do
			if ds.has (g) then
				Result := TRUE
			end
		end

	in_range (h: H; rs: SET[H]): BOOLEAN
		do
			if rs.has (h) then
				Result := TRUE
			end
		end

	in_either_fun (p: PAIR[G, h]; f1, f2: FUN[G, H]): BOOLEAN
		do
			Result := f1.has (p) OR ELSE f2.has (p)
		end

	in_both_fun (p: PAIR[G, h]; f1, f2: FUN[G, H]): BOOLEAN
		do
			Result := f1.has (p) AND THEN f2.has (p)
		end

feature -- Outputs

	debug_output: STRING
		do
			Result := out
		end

	out: STRING
		do
			Result := as_set.out
		end

invariant
	is_a_function:
		is_function
end
