note
	description: "RELATION data structure for both specification and implementation."
	author: "JSO and JWs"
	date: "$Date$"
	revision: "$Revision$"

class
	REL[G -> attached ANY, H -> attached ANY]
inherit
	SET[PAIR[G, H]]
		rename
			as_array as set_as_array
		end

create
	make_empty,
	make_from_tuple_array

-- commented out due to an unresolved issue:
--  https://www2.eiffel.com/support/protected/report.aspx?pr=19050
convert
	make_from_tuple_array ({attached ARRAY[TUPLE[G, H]]})

feature -- Constructor

	make_from_tuple_array (a: ARRAY[TUPLE[fst: G; snd: H]])
		do
			make_empty
			across
				a as tup
			loop
				extend (
					create {PAIR[G, H]}.make_from_tuple (tup.item))
			end
		end

feature -- Conversion to array.

	as_array: ARRAY[TUPLE [G,H]]
		do
			create Result.make_empty
			across
				Current as c
			loop
				Result.force (c.item.as_tuple, Result.upper + 1)
			end
			Result.compare_objects
		ensure
			Current ~ create {REL[G,H]}.make_from_tuple_array (Result)
			-- why does this fail in {REL}.t8
		end

feature -- Commands for relational operations

	domain_restrict (ds: SET[G])
			-- Keep all pairs whose first values are members of 'ds'.
		do
			domain_subtract (domain |\ ds)
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_ds_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).domain ~ (old Current.deep_twin.domain |\ ds)
		end

	domain_restrict_by (g: G)
			-- Keep pairs whose first values are 'd'.
		do
			domain_subtract (domain - g)
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_g_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).domain ~ (old Current.deep_twin.domain |\ singleton_g (g))
		end

	range_restrict (rs: SET[H])
			-- Keep all pairs whose second values are members of 'rs'.
		do
			range_subtract (range |\ rs)
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_rs_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).range ~ (old Current.deep_twin.range |\ rs)
		end

	range_restrict_by (h: H)
			-- Keep all pairs whose second values are 'h'.
		do
			range_subtract (range |\ singleton_h (h))
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			only_h_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).range ~ (old Current.deep_twin.range |\ singleton_h (h))
		end

	domain_subtract (ds: SET[G])
			-- Subtract all pairs whose first values are members of 'ds'.
		local
			g: G
		do
			from
				imp.start
			until
				imp.after
			loop
				g := imp.item.first
				if ds.has (g) then
					imp.remove
				else
					imp.forth
				end
			end
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_ds_in_new_rel:
				-- in case 'ds' contains items not in the domain
				( (old Current.deep_twin) |\ (Current) ).domain ~
					ds.comprehension (agent in_domain (?, (old Current.deep_twin).domain))
		end

	domain_subtract_by (g: G)
			-- Subtract pairs whose first values are 'g'.
		do
			domain_subtract (create {SET[G]}.make_from_array (<<g>>))
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_g_in_new_rel:
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
				imp.start
			until
				imp.after
			loop
				h := imp.item.second
				if rs.has (h) then
					imp.remove
				else
					imp.forth
				end
			end
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_rs_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).range ~
					-- in case 'rs' contains items not in the range
					rs.comprehension (agent in_range (?, (old Current.deep_twin).range))
		end

	range_subtract_by (h: H)
			-- Subtract pairs whose second values are 'h'.
		do
			range_subtract (create {SET[H]}.make_from_array (<<h>>))
		ensure
			new_rel_is_a_subset:
				Current |<: (old Current.deep_twin)
			no_h_in_new_rel:
				( (old Current.deep_twin) |\ (Current) ).range ~
					-- in case 'h' is not in the range
					singleton_h (h).comprehension (agent in_range (?, (old Current.deep_twin).range))
		end

	override (r: like Current)
			-- Update current relation such that it aggres on 'r'.
		do
			domain_subtract (r.domain)
			union (r)
		ensure
			Current ~ ( (old Current.deep_twin |<< r.domain) |\/| r )
		end

	override_by (t: TUPLE[g: G; h: H])
			-- Update current relation such that it aggres on 'g |-> h'.
		do
			domain_subtract_by (t.g)
			extend (create {PAIR[G, H]}.make_from_tuple (t))
		ensure
			Current ~ ( (old Current.deep_twin @<< t.g) |\/| singleton_gh (t.g, t.h) )
		end

feature -- Status queries

	is_function: BOOLEAN
			-- Is current relation a function?
			-- i.e., each domain value maps to at most one value.
		local
			c: ITERATION_CURSOR[PAIR[G, H]]
		do
			from
				Result := TRUE
				c := new_cursor
			until
				not Result OR ELSE c.after
			loop
				if # image (c.item.first) > 1 then
					Result := False
				end
				c.forth
			end
		ensure
			Result = across domain as d all # image (d.item) = 1 end
		end

	is_injection: BOOLEAN
			-- Is current relation an injective function?
			-- i.e., no two domain values map to the same range vaule.
		do
			Result := is_function and then inverse.is_function
		ensure
			Result = (is_function and inverse.is_function)
		end

	domain: SET[G]
			-- Return the domain set of relation.
		do
			create Result.make_empty
			across Current as c loop
				Result.extend (c.item.first)
			end
		end

	range: SET[H]
			-- Return the range set of relation.
		do
			create Result.make_empty
			across Current as c loop
				Result.extend (c.item.second)
			end
		end

feature -- Queries for relational operations

	inverse: REL[H, G]
		do
			create Result.make_empty
			across
				Current as pair
			loop
				Result.extend (
					create {PAIR[H, G]}.make_from_tuple (
						[pair.item.second, pair.item.first]))
			end
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin

			Result.inverse.is_equal (Current)
		end

	image alias "[]"(g: G): SET[H]
			-- Retrieve the set of items that are associated with 'g'.
		do
			create Result.make_empty
			across
				Current as c
			loop
				if c.item.first ~ g then
					Result.extend (c.item.second)
				end
			end
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			Result.is_empty implies not domain.has (g)
			across Result as r
				all
					has (create {PAIR[G, H]}.make_from_tuple ([g, r.item]))
				end
			across range.differenced (Result) as r
				all
					not has (create {PAIR[G, H]}.make_from_tuple ([g, r.item]))
				end
		end

	domain_restricted alias "|<" (ds: SET[G]): like Current
			-- Return a copy of current relation with
			-- all pairs whose first values are members of 'ds' kept.
		do
			Result := Current.deep_twin
			Result.domain_restrict (ds)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			only_ds_in_new_rel:
				( Current |\ Result ).domain ~ (domain |\ ds)
		end

	domain_restricted_by alias "@<" (g: G): like Current
			-- Return a copy of current relation with
			-- all pairs whose first values are 'g' kept.
		do
			Result := Current.deep_twin
			Result.domain_restrict_by (g)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			only_g_in_new_rel:
				( Current |\ Result ).domain ~ (domain |\ singleton_g (g))
		end

	range_restricted alias "|>" (rs: SET[H]): like Current
			-- Return a copy of current relation with
			-- all pairs whose second values are members of 'rs' kept.
		do
			Result := Current.deep_twin
			Result.range_restrict (rs)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			only_rs_in_new_rel:
				( Current |\ Result ).range ~ (range |\ rs)
		end

	range_restricted_by alias "@>" (h: H): like Current
			-- Return a copy of current relation with
			-- all pairs whose second values are 'h' kept.
		do
			Result := Current.deep_twin
			Result.range_restrict_by (h)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			only_h_in_new_rel:
				( Current |\ Result ).range ~ (range |\ singleton_h (h))
		end

	domain_subtracted alias "|<<" (ds: SET[G]): like Current
			-- Return a new copy of current relation with
			-- all pairs whose first values are members of 'ds' subtracted.
		do
			Result := Current.deep_twin
			Result.domain_subtract (ds)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			no_ds_in_new_rel:
				( Current |\ Result ).domain ~
					-- in case 'ds' contains items not in the domain
					ds.comprehension (agent in_domain (?, domain))
		end

	domain_subtracted_by alias "@<<" (g: G): like Current
			-- Return a new copy of current relation with
			-- all pairs whose first values 'g' subtracted.
		do
			Result := Current.deep_twin
			Result.domain_subtract_by (g)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			no_ds_in_new_rel:
				( Current |\ Result ).domain ~
					-- in case 'g' is not in the domain
					singleton_g (g).comprehension (agent in_domain (?, domain))
		end

	range_subtracted alias "|>>" (rs: SET[H]): like Current
			-- Return a new copy of current relation with
			-- all pairs whose second values are members of 'ds' subtracted.
		do
			Result := Current.deep_twin
			Result.range_subtract (rs)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			no_rs_in_new_rel:
				( Current |\ Result ).range ~
					-- in case 'rs' contains items not in the range
					rs.comprehension (agent in_range (?, range))
		end

	range_subtracted_by alias "@>>" (h: H): like Current
			-- Return a new copy of current relation with
			-- all pairs whose second values are 'h' subtracted.
		do
			Result := Current.deep_twin
			Result.range_subtract_by (h)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			new_rel_is_a_subset:
				Result |<: Current
			no_rs_in_new_rel:
				( Current |\ Result ).range ~
					-- in case 'h' is not in the range
					singleton_h (h).comprehension (agent in_range (?, range))
		end

	overriden alias "|<+" (r: like Current): like Current
			-- Return a copy of current relation that agrres on 'r'.
		do
			Result := Current.deep_twin
			Result.override (r)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			Result ~ ( (Current |<< r.domain) |\/| r )
		end

	overriden_by alias "@<+" (t: TUPLE[g: G; h: H]): like Current
			-- Return a copy of current relation that agrres on 'g |-> h'.
		do
			Result := Current.deep_twin
			Result.override_by (t.g, t.h)
		ensure
			current_rel_unchanged:
				Current ~ old Current.deep_twin
			Result ~ ( (Current @<< t.g) |\/| singleton_gh (t.g, t.h) )
		end

feature -- Agent functions

	in_domain (g: G; dom: SET[G]): BOOLEAN
		do
			if dom.has (g) then
				Result := TRUE
			end
		end

	in_range (h: H; ran: SET[H]): BOOLEAN
		do
			if ran.has (h) then
				Result := TRUE
			end
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

	singleton_gh (g: G; h: H): REL[G, H]
		do
			create Result.make_from_tuple_array (<<[g, h]>>)
		ensure
			# Result = 1
		end
end
