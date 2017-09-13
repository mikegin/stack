note
	description: "SET data structure for both specification and implementation."
	author: "JSO and JW"

class
	SET[G -> attached ANY]
inherit
	ITERABLE[G]
		undefine
			is_equal,
			out
		end

	DEBUG_OUTPUT
		redefine
			is_equal,
			out
		end

create
	make_empty,
	make_from_array

-- commented out due to an unresolved issue:
--  https://www2.eiffel.com/support/protected/report.aspx?pr=19050
convert
	make_from_array ({ ARRAY[G]})
	, as_array: {ARRAY[G]}

feature {SET} -- Implementation

	imp: ARRAYED_LIST[G]

	item_imp: detachable CELL [G]

	set_imp (other_imp: like imp)
		do
			imp := other_imp

			if not imp.object_comparison then
				imp.compare_objects
			end
		end

	void_item
		once
			item_imp := Void
		end

feature -- Constructor

	make_empty
			-- Initialize an empty set.
		do
			create imp.make (0)
			imp.compare_objects
		ensure
			is_empty
		end

	make_from_array (a: ARRAY[G])
		do
			make_empty
			across
				a as it
			loop
				extend (it.item)
			end
			imp.compare_objects
		ensure
			all_items_are_intended:
				across
					Current as it
				all
					a.has (it.item)
				end
			all_intended_items_added:
				across
					a as it
				all
					Current.has (it.item)
				end
		end

feature -- Conversion to array.

	as_array: ARRAY[G]
		do
			create Result.make_empty
			across
				Current as c
			loop
				Result.force (c.item, Result.upper + 1)
			end
--			Result.compare_objects
		ensure
			Current ~ create {SET[G]}.make_from_array (Result)
			-- why does this fail in {REL}.t8
		end

feature -- Iteration

	new_cursor: ITERATION_CURSOR[G]
		do
			Result := imp.new_cursor
		end

feature -- Query and command for arbitrary set members

	chosen: BOOLEAN
		do
			Result := attached item_imp
		end

	item : G
			-- Return an arbitrary member from the set.
		require
			not is_empty
			chosen
		do
			check attached item_imp as l_item then
				Result := l_item.item
			end
		ensure
			has (Result)
		end

 	choose_item
 			-- Choose an arbitrary element of the
 			-- set and store it in `item'
 		require
 			not is_empty
 		do
 			create item_imp.put (imp [count])
 		ensure
 			has (item)
			chosen
 		end

	remove_item
			-- Remove an arbitrary member (i.e., 'item') from the set.
		require
			not is_empty
			chosen
		do
			imp.go_i_th (count)
			imp.remove
			item_imp := Void
		ensure
			Current ~ old Current.deep_twin - old item
			not chosen
		end

feature -- Commands for implementation

	extend (g: G)
			-- Extend the current set by 'g'.
		do
			if not has (g) then
				imp.extend (g)
			end
			void_item
		ensure
			case_of_no_extension:
				(old Current.deep_twin).has (g) implies
					old Current.deep_twin ~ Current
			case_of_extension:
				not (old Current.deep_twin).has (g) implies
					old Current.deep_twin ~ Current - g
		end

	union (other: like Current)
			-- Extend the current set by 'other'.
		do
			across
				other as it
			loop
				extend (it.item)
			end
			void_item
		ensure
			old Current.deep_twin |<: Current
			other |<: Current
			definition:
				hold_count (
					agent in_either_set (?, old Current.deep_twin, other)) = count
		end

	subtract (g: G)
			-- Subtract the current set by 'g'.
		do
			from
				imp.start
			until
				imp.after
			loop
				if imp.item ~ g then
					imp.remove
				else
					imp.forth
				end
			end
			void_item
		ensure
			case_of_subtraction:
				(old Current.deep_twin).has (g) implies
					old Current.deep_twin ~ Current + g
			case_of_no_subtraction:
				not (old Current.deep_twin).has (g) implies
					old Current.deep_twin ~ Current
		end

	difference (other: like Current)
			-- Subtract the current set by 'other'.
		do
			across
				other as it
			loop
				subtract (it.item)
			end
			void_item
		ensure
			definition:
				old Current.deep_twin ~
					Current |\/| (old Current.deep_twin |/\| other)
		end

	intersect (other: like Current)
			-- Intersect current set with 'other'.
		do
			from
				imp.start
			until
				imp.after
			loop
				if not other.has (imp.item) then
					imp.remove
				else
					imp.forth
				end
			end
			void_item
		ensure
			Current |<: old Current.deep_twin
			Current |<: other
			definition:
				hold_count (
					agent in_both_set (?, old Current.deep_twin, other)) = count
		end

feature -- Queries for specification.

	count alias "#": INTEGER
			-- Return the cardinality of the set.
		do
			Result := imp.count
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			definition:
				Result = hold_count (agent g_to_true)
		end

	is_empty : BOOLEAN
			-- Is the set empty?
		do
			Result := (count = 0)
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			Result = (# Current = 0)
		end

	has (g: G): BOOLEAN
			-- Does the set contain 'g'?
		do
			Result := (imp.has (g))
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			definition_1:
				Result =
					(hold_count (agent eq (?, g)) = 1)
			definition_2:
				Result =
					across
						Current as it
					some
						it.item ~ g
					end
		end

	is_subset_of alias "|<:" (other: like Current): BOOLEAN
		local
			i : INTEGER
		do
			from
				Result := TRUE
				i := imp.lower
			until
				NOT Result OR ELSE i > imp.upper
			loop
				Result := other.has (imp [i])
				i := i + 1
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			Result =
				across
					Current as cur
				all
					other.has (cur.item)
				end
		end

	extended alias "+" (g: G): like Current
			-- Return a new set representing the addtion of current and 'g'.
		do
			create Result.make_empty
			Result.set_imp (Current.imp.twin)
			Result.extend (g)
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			case_of_no_extension:
				has (g) implies Current ~ Result
			case_of_extension:
				not has (g) implies Current ~ Result - g
		end

	unioned alias "|\/|" (other: like Current): like Current
			-- Return a new set representing the union of current and 'other'.
		do
			create Result.make_empty
			Result.set_imp (Current.imp.twin)

			across
				other as it
			loop
				Result.extend (it.item)
			end
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			items_from_either_set:
				across
					Result as it
				all
					Current.has (it.item) OR other.has (it.item)
				end
		end

	subtracted alias "-" (g: G): like Current
			-- Return a new set representing the difference between Current and 'other'.
		do
			create Result.make_empty
			Result.set_imp (Current.imp.twin)
			Result.subtract (g)
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			case_of_subtraction:
				has (g) implies Current ~ Result + g
			case_of_no_subtraction:
				not has (g) implies Current ~ Result
		end

	differenced alias "|\" (other: like Current): like Current
			-- Return a new set representing the difference between Current and 'other'.
		local
			new_imp: ARRAYED_LIST[G]
		do
			create new_imp.make (0)

			across
				imp as src
			loop
				if not other.has (src.item) then
					new_imp.extend (src.item)
				end
			end

			create Result.make_empty
			Result.set_imp (new_imp)
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			definition:
				Current ~ Result |\/| (Current |/\| other)
		end

	intersected alias "|/\|" (other: like Current): like Current
			-- Return a new set representing the intersection of current and 'other'.
		do
			create Result.make_empty

			across
				other as it
			loop
				if has (it.item) then
					Result.extend (it.item)
				end
			end
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			items_from_both_set:
				across
					Result as it
				all
					Current.has (it.item) AND other.has (it.item)
				end
		end

feature -- Quantifiers

   hold_count (exp: PREDICATE [G]): INTEGER
			-- How many items satisfying `exp' are in `Current'?
		local
			i: INTEGER
		do
			from
				i := imp.lower
			until
				i > imp.upper
			loop
				if exp.item ([imp[i]]) then
					Result := Result + 1
				end
				i := i + 1
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			maximum_result: Result <= count
		end

	comprehension alias "|" (exp: PREDICATE [G]): like Current
			-- Largest subset of the current set whose elements satisfy `exp'
			-- e.g. for set: MSL_SET[STRING],
			-- (set | agent {STRING}.has_substring ("xy")) = {g:set | g.has_substring("xy")}
		local
			i: INTEGER
			imp_item: G
		do
			create Result.make_empty
			from
				i := imp.lower
			until
				i > imp.upper
			loop
				imp_item := imp[i]
				if exp.item ([imp_item]) then
					Result.extend (imp_item)
				end
				i := i + 1
			end
			Result.void_item
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			is_subset: Result |<: Current
			all_satisfying_exp: Result.hold_count (exp) = # Result
			consistent_satisfying_items: Current.hold_count (exp) = # Result
		end

feature -- Equality

	is_equal (other: like Current): BOOLEAN
			-- Is curren set equal to 'other'?
		do
				Result :=
					# Current = # other
					and then
					other   |<: Current
				 	and then
				 	Current |<: other
		ensure then
			Result =
				(Current |<: other
				 and then
				 other   |<: Current)
		end

feature {SET} -- agent functions

	g_to_true (v: G): BOOLEAN
		do
			Result := True
		ensure
			definition: Result
		end

	eq (v1, v2: G): BOOLEAN
		do
			--Result := equal (v1, v2)
			Result := v1 ~ v2
		end

	in_either_set (g: G; s1, s2: SET[G]): BOOLEAN
		do
			Result := s1.has (g) OR ELSE s2.has (g)
		end

	in_both_set (g: G; s1, s2: SET[G]): BOOLEAN
		do
			Result := s1.has (g) AND THEN s2.has (g)
		end

feature -- Debug output

	debug_output: STRING
		do
			Result := out
		end

	out: STRING
		local
			i: INTEGER
		do
			create Result.make_empty
			Result.append ("{ ")
			from
				i := imp.lower
			until
				i > imp.upper
			loop
				check attached {G} imp[i] as e then
					Result.append (e.out)
				end
				if i < imp.upper then
					Result.append (", ")
				end
				i := i + 1
			end
			Result.append (" }")
		end

invariant
		imp.object_comparison

	no_duplicates:
		across
			imp.lower |..| imp.upper as i
		all
			across
				imp.lower |..| imp.upper as j
			all
				imp[i.item] ~ imp[j.item] IMPLIES i.item = j.item
			end
		end
end
