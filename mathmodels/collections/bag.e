note
	description: "Collections with membership multilicity"
	author: "Jackie Wang"
	date: "$Date$"
	revision: "$Revision$"

class
	BAG[G -> attached ANY]
inherit

	ITERABLE[PAIR[G, INTEGER]]
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
	make_from_array,
	make_from_tuple_array

feature -- Constructor

	make_empty
		do
			create imp.make_empty
		end

	make_from_array (a: ARRAY[G])
		do
			make_empty
			across
				a as it
			loop
				extend_by (it.item)
			end
		ensure
			# Current = a.count
		end

	make_from_tuple_array (a: ARRAY[TUPLE[g: G; i: INTEGER]])
		require
			across a as cur all
				cur.item.i > 0
			end
		local
			new_count: INTEGER
		do
			make_empty
			across
				a as t
			loop
				new_count := Current[t.item.g] + t.item.i
				imp.override (create {FUN[G, INTEGER]}.make_from_array (
								<<[t.item.g, new_count]>>))
			end
		end

feature -- Iteration cursor

	new_cursor: ITERATION_CURSOR[PAIR[G, INTEGER]]
		do
			Result := imp.new_cursor
		end

feature -- Conversion

	as_function: FUN[G, INTEGER]
			-- Return current bag as a function from items
			-- to number of occurrences.
		local
			pair: PAIR[G, INTEGER]
		do
			create Result.make_empty
			across
				imp as cur
			loop
				create pair.make (cur.item.first, cur.item.second)
				Result.extend (pair)
			end
		ensure
			all_bag_items_covered:
				across Current as cur all
					Current[cur.item.first] = Result[cur.item.first]
				end
			only_bag_items_covered:
				across Result as cur all
					Current[cur.item.first] = Result[cur.item.first]
				end
		end

	as_set: SET[G]
			-- Return the domain of curret bag
		do
			create Result.make_empty
			across
				imp as cur
			loop
				Result.extend (cur.item.first)
			end
		ensure
			Result ~ as_function.domain
		end

	as_array: ARRAY[G]
			-- Return current bag as an array of items.
		local
			i: INTEGER
		do
			create Result.make_empty
			across
				imp as map
			loop
				from
					i := 1
				until
					i > map.item.second
				loop
					Result.force (map.item.first, Result.upper + 1)
					i := i + 1
				end
			end
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			same_count:
				Result.count = # Current
		end

feature -- Status queries

	count alias "#": INTEGER
		do
			Result := 0
			across
				imp as map
			loop
				Result := Result + map.item.second
			end
		ensure
			Result = as_array.count
		end

	occurrences alias "[]" (g: G): INTEGER assign override
			-- Number of 'g' in current bag.
		do
			if imp.domain.has (g) then
				Result := imp[g]
			else
				Result := 0
			end
		ensure
			non_negative_occurrences:
				Result >= 0
			case_of_nonmember:
				not has (g) IMPLIES Result = 0
			case_of_member:
				has (g) IMPLIES Result > 0 and Result = as_function [g]
		end

	is_empty: BOOLEAN
		do
			Result := # Current = 0
		ensure
			Result = (# Current = 0)
		end

	has (g: G): BOOLEAN
		do
			Result := imp.domain.has (g)
		ensure
			Result = as_array.has (g)
			Result = as_function.domain.has (g)
			Result = (Current[g] > 0)
		end

	is_subbag_of alias "|<:" (other: like Current): BOOLEAN
		local
			fun_cur: ITERATION_CURSOR[PAIR[G, INTEGER]]
			item: G
			occ: INTEGER
		do
			Result := TRUE
			from
				fun_cur := imp.new_cursor
			until
				not Result OR ELSE fun_cur.after
			loop
				item := fun_cur.item.first
				occ := fun_cur.item.second
				if other[item] < occ then
					Result := FALSE
				end
				fun_cur.forth
			end
		ensure
			Result =
				across as_function as cur all
					cur.item.second <= other[cur.item.first]
				end
		end

feature -- Commands

	override (i: INTEGER; g: G)
			-- Change quantity of 'g' to 'i' in current bag
		do
			imp.override (
				create {FUN[G, INTEGER]}.make_from_array (
					<<[g, i]>>))
		ensure
			Current ~ old Current.deep_twin.overriden (i, g)
		end

	extend (g: G; i: INTEGER)
			-- Add 'g' of quantity 'i' into current bag.
		local
			new_count: INTEGER
		do
			if imp.domain.has (g) then
				new_count := imp[g] + i
			else
				new_count := i
			end
			imp.override (
				create {FUN[G, INTEGER]}.make_from_array (
					<<[g, new_count]>>))
		ensure
			Current ~ old Current.deep_twin.extended (g, i)
		end

	extend_by (g: G)
			-- Add 'g' of quantity 1 into current bag.
		do
			extend (g, 1)
		ensure
			Current ~ old Current.deep_twin.extended_by (g)
		end

	union (other: like Current)
			-- Add 'other' into current bag.
		do
			across
				other.imp as cur
			loop
				extend (cur.item.first, cur.item.second)
			end
		ensure
			Current ~ old Current.deep_twin.unioned (other)
		end

	subtract (g: G; i: INTEGER)
			-- Subtract 'g' of quantity 'i' from current bag.
		require
			Current[g] >= i
		local
			old_count: INTEGER
		do
			old_count := imp[g]

			if old_count = i then
				imp.subtract (create {PAIR[G, INTEGER]}.make (g, old_count))
			else
				imp.override (
					create {FUN[G, INTEGER]}.make_from_array (
						<<[g, old_count - i]>>))
			end
		ensure
			Current ~ old Current.deep_twin.subtracted (g, i)
		end

	subtract_by (g: G)
			-- Subtract 'g' of quantity 1 from current bag.
		require
			Current[g] >= 1
		do
			subtract (g, 1)
		ensure
			Current ~ old Current.deep_twin.subtracted_by (g)
		end

	difference (other: like Current)
			-- Subtract 'other' from current bag.
		require
			other |<: Current
		do
			across
				other.imp as cur
			loop
				subtract (cur.item.first, cur.item.second)
			end
		ensure
			Current ~ old Current.deep_twin.differenced (other)
		end

feature -- Specification Queries

	overriden (i: INTEGER; g: G): like Current
			-- Return a representation of current bag with
			-- quantity of 'g' to 'i'
		do
			Result := Current.deep_twin
			Result.override (i, g)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(cur.item.first ~ g implies
					Result[cur.item.first] = i)
				and
				(cur.item.first /~ g implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	extended (g: G; i: INTEGER): like Current
			-- Return a representation of current bag with
			-- 'g' of quantity 'i' added.
		do
			Result := Current.deep_twin
			Result.extend (g, i)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(cur.item.first ~ g implies
					Result[cur.item.first] = Current[cur.item.first] + i)
				and
				(cur.item.first /~ g implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	extended_by alias "+" (g: G): like Current
			-- Return a representation of current bag with
			-- 'g' of quantity 1 added.
		do
			Result := Current.deep_twin
			Result.extend_by (g)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(cur.item.first ~ g implies
					Result[cur.item.first] = Current[cur.item.first] + 1)
				and
				(cur.item.first /~ g implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	unioned alias "|\/|" (other: like Current): like Current
			-- Return a representation of current bag with
			-- 'other' added.
		do
			Result := Current.deep_twin
			Result.union (other)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(other.has(cur.item.first) implies
					Result[cur.item.first] = Current[cur.item.first] + other[cur.item.first])
				and
				(not other.has (cur.item.first) implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	subtracted (g: G; i: INTEGER): like Current
			-- Return a representation of current bag with
			-- 'g' of quantity 'i' subtracted.
		require
			Current[g] >= i
		do
			Result := Current.deep_twin
			Result.subtract (g, i)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(cur.item.first ~ g implies
					Result[cur.item.first] = Current[cur.item.first] - i)
				and
				(cur.item.first /~ g implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	subtracted_by alias "-" (g: G): like Current
			-- Return a representation of current bag with
			-- 'g' of quantity 1 subtracted.
		require
			Current[g] >= 1
		do
			Result := Current.deep_twin
			Result.subtract_by (g)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(cur.item.first ~ g implies
					Result[cur.item.first] = Current[cur.item.first] - 1)
				and
				(cur.item.first /~ g implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

	differenced alias "|\" (other: like Current): like Current
			-- Return a representation of current bag with
			-- 'other' subtracted.
		require
			other |<: Current
		do
			Result := Current.deep_twin
			Result.difference (other)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			across
				Result as cur
			all
				(other.has(cur.item.first) implies
					Result[cur.item.first] = Current[cur.item.first] - other[cur.item.first])
				and
				(not other.has (cur.item.first) implies
					Result[cur.item.first] = Current[cur.item.first])
			end
		end

feature -- Quantifiers

	hold_count (exp: PREDICATE [PAIR[G, INTEGER]]): INTEGER
			-- How many items satisfying `exp' are in `Current'?
		do
			Result := as_function.hold_count (exp)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			maximum_result: 0 <= Result and Result <= count
			0 <= Result and Result <= # as_function.domain
		end

	comprehension alias "|" (exp: PREDICATE [PAIR[G, INTEGER]]): like Current
			-- Largest subset of the current fun whose elements satisfy `exp'
		local
			fun: FUN[G, INTEGER]
		do
			fun := as_function.comprehension (exp)
			create Result.make_empty
			Result.set_imp (fun)
		ensure
			current_bag_unchanged:
				Current ~ old Current.deep_twin
			is_subset: Result |<: Current
			all_satisfying_exp: Result.hold_count (exp) = # Result.as_set
			consistent_satisfying_items: Current.hold_count (exp) = # Result.as_set
		end

feature -- Equality

	is_equal (other: like Current): BOOLEAN
		do
			Result :=
				# Current = # other and then
				imp ~ other.imp
		ensure then
			Result = (Current |<: other and other |<: Current)
			Result = (as_function ~ other.as_function)
		end

feature -- Output

	out: STRING
			-- Return a string representation of current bag
		do
			Result := imp.out
		ensure then
			Result ~ as_function.out
		end

	debug_output: STRING
			-- Return a string representation of current bag
			-- for debugging
		do
			Result := out
		ensure then
			Result ~ out
		end

feature {BAG} -- Implementation

	imp: FUN[G, INTEGER]

	set_imp (new_imp: like imp)
		do
			imp := new_imp
		ensure
			imp = new_imp
		end

invariant

	bag_not_containing_zero_occurrence_item:
		across
			Current as pair
		all
			pair.item.second > 0
		end
end
