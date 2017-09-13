note
	description: "[
		(1) Model contracts for finite sequences for elements of type G.
		(2) Queries are side effect free and return sequences via 
		    deep_twin; thus inefficient (use only for contracts).
		(3) Commands change the current sequence. 
		(4) A valid index is 1..count.
		(5) Array notation can be used, as well as iteration (across).
		(6) Empty sequences can be created, or creation can be from an array. 
		(7) Sequences have a first item (the head), a tail and last item.
		(8) Infix notation for prepended_by(x:G):
			seq1 |< x
		(9) Infix notation for appended_by(x:G):
			seq1 |> x
		(10) For concatenation may use infix: seq1 |++| seq2
		(11) For queries, to assert that the state is not changed, 
		the postcondition is
			Current ~ old Current.deep_twin
		]"
	author: "JSO"
	date: "$Date$"
	revision: "$Revision$"

class
	SEQ[G -> attached ANY]
inherit

	ITERABLE[G]
		redefine
			is_equal,
			out
		end

	DEBUG_OUTPUT
		undefine
			is_equal,
			out
		end

create
	make_empty,
	make_from_array

feature -- 2-level copy
	twin2: like Current
		do
			Result := Current.twin
			Result.set_imp (Current.imp.twin)
		end

feature -- Constructors

	make_empty
			-- create empty list
		do
			create imp.make (10)
			imp.compare_objects
		ensure
			is_empty: is_empty
		end

	make_from_array (a: ARRAY [G])
			-- Create list from array `a'.

		do
			--implementation
			create imp.make_from_array (a)
			imp.compare_objects
		ensure
			# Current = a.count
			across
				a.lower |..| a.upper as i
			all
				Current [i.item - a.lower + 1] ~ a [i.item]
			end
		end

feature -- Iteration

	new_cursor: ITERATION_CURSOR[G]
			-- A new cursor for iterating through current sequence
		do
			Result := imp.new_cursor
		end

feature -- Status Queries

	count alias "#": INTEGER
			-- Return the number of elements in current sequence
		do
			Result := imp.count
		ensure
			Result = as_array.count
			Result = # as_function
		end

	lower: INTEGER
			-- Starting position of current sequence
		do
			Result := 1
		ensure
			Result = 1
		end

	upper: INTEGER
			-- Ending position of current sequence
		do
			Result := count
		ensure
			Result = # Current
		end

	is_empty: BOOLEAN
			-- Is the current sequence empty?
		do
			Result := count = 0
		ensure
			Result = (# Current = 0)
			Result = as_array.is_empty
			Result = as_function.is_empty
		end

	has(v: G): BOOLEAN
			-- Does 'v' exist in current sequence?
		do
			Result := imp.has (v)
		ensure
			Result =
				across 1 |..| count as i
				some Current[i.item] ~ v
				end
		end

	first : G
			-- Return the 1st element in current sequence
		require
			not is_empty
		do
			Result := imp[imp.lower]
		ensure
			Result ~ as_array[1]
			Result ~ as_function[1]
		end

	front : like Current
			-- Return current sequence except the last element
		require
			not is_empty
		do
			if count > 1 then
				Result := subsequenced (1, count - 1)
			else
				create Result.make_empty
			end
		ensure
			case_of_empty_init:
				# Current = 1 IMPLIES Result.is_empty
			case_of_nonempty_init:
				# Current > 1 IMPLIES Result ~ subsequenced (1, count - 1)
		end

	last : G
			-- Return the last element in current sequence
		require
			not is_empty
		do
			Result := imp[imp.upper]
		ensure
			Result ~ as_array[count]
			Result ~ as_function[count]
		end

	tail : like Current
			-- Return current sequence except the first element
		require
			not is_empty
		do
			if count > 1 then
				Result := subsequenced (2, count)
			else
				create Result.make_empty
			end
		ensure
			case_of_empty_tail:
				# Current = 1 IMPLIES Result.is_empty
			case_of_nonempty_tail:
				# Current > 1 IMPLIES Result ~ subsequenced (2, count)
		end

	item alias "[]" (i: INTEGER): G assign override
			-- Element at `i'-th position
		require
			valid_position (i)
		do
			Result := imp.i_th (i)
		ensure
			Result ~ as_function [i]
			Result ~ as_array [i]
		end

	is_subsequence_of alias "|<:"(other: like Current): BOOLEAN
			-- Is current a contiguous subsequence of 'other'?
			-- subsequences are not necessarily contiguous
			-- e.g. subsequences of <2, 3, 8, 5, 2> are:
			-- <>, <3, 5> <3, 5, 2> etc.
		local
			proj: SEQ[G]
			ran: SET[G]
			element: G
		do
			-- project 'other' to the range of Current sequence
			ran := Current.as_function.range
			create proj.make_empty
			across
				other as o
			loop
				element := o.item
				if ran.has (element) then
					proj.append (element)
				end
			end

			Result := is_augmented_subseq_of (
						augmented_with_collapsed_rep,
						proj.augmented_with_collapsed_rep)
		end

	is_contiguous_subseq_of (other: like Current): BOOLEAN
			-- Is current a contiguous subsequence of 'other'?
			-- e.g. contiguous subsequences of <2, 3, 8, 5, 2> are:
			-- <>, <2, 3> <3, 8, 5> etc.
		do
			Result := is_augmented_subseq_of (
						augmented_without_collapsed_rep,
						other.augmented_without_collapsed_rep)
		ensure
			case_current_empty:
				is_empty IMPLIES Result
			case_other_empty:
				other.is_empty IMPLIES
					Result = is_empty
			case_both_non_empty:
				NOT (is_empty OR other.is_empty) IMPLIES
					Result =
						(across 1 |..| # other as start_pos some
						 across 1 |..| # other as end_pos   some
							end_pos.item >= start_pos.item AND
								Current ~ other.subsequenced (
									start_pos.item, end_pos.item)
					 	end
					 	end)
		end

feature -- Commands

	append (v: G)
			-- Add `v' to end.
		do
			imp.extend(v)
		ensure
			Current ~ old Current.deep_twin.appended (v)
		end


	prepend(v: G)
			-- Add `v' to beginning.
		do
			imp.put_front (v)
		ensure
			Current ~ old Current.deep_twin.prepended (v)
		end

	subsequence (i, j: INTEGER)
			-- Cut down current seq so that segment i..j remains
		require
			valid_position (i)
			valid_position (j)
		local
			pos: INTEGER
		do
			if i <= j then
				from
					pos := 1
					imp.start
				until
					imp.after
				loop
					if pos < i OR pos > j then
						imp.remove
					else
						imp.forth
					end
					pos := pos + 1
				end
			else
				make_empty
			end
		ensure
			Current ~ old Current.deep_twin.subsequenced (i, j)
		end

	concatenate (other: like Current)
			-- Append 'other' to the end of current sequence
		do
			across
				other as cur
			loop
				append (cur.item)
			end
		ensure
			Current ~ old Current.deep_twin.concatenated (other)
		end

	override (v: G; i: INTEGER_32)
			-- Replace `i'-th entry, if in index interval, by `v'.
		require
			valid_position (i)
		do
			imp.put_i_th (v, i)
		ensure
			Current ~ old Current.deep_twin.overriden (v, i)
		end

	insert (v: G; i: INTEGER)
			-- Insert 'v' as the `i'-th entry, if in index interval
			-- e.g., insert(1) on an empty sequence is forbidden.
		require
			valid_position (i)
		local
			j: INTEGER
			done: BOOLEAN
		do
			from
				imp.start
				j := 1
			until
				done
			loop
				if j = i then
					imp.put_left (v)
					done := TRUE
				else
					-- do nothing, proceed with the counting
				end
				imp.forth
				j := j + 1
			end
		ensure
			Current ~ old Current.deep_twin.inserted (v, i)
		end

	remove (i:INTEGER)
			-- Remove `i'-th entry, if in index interval
		require
			valid_position (i)
		do
			imp.start
			if imp.count > 1 then
				imp.move (i-1)
			end
			imp.remove
		ensure
			Current ~ old Current.deep_twin.removed (i)
		end

	reverse
			-- Reverse the order of current sequence
		local
			new_imp: like imp
		do
			create new_imp.make_filled (count)
			new_imp.compare_objects
			across
				1 |..| count as i
			loop
				new_imp[count - i.item + 1] := Current[i.item]
			end
			set_imp (new_imp)
		ensure
			Current ~ old Current.deep_twin.reversed
		end

feature -- Specification Queries

	appended alias "|->"(v: G): like Current
			-- Return a sequence representing current with 'v' added to end
		do
			Result := Current.deep_twin
			Result.append (v)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_incremented:
				# Result = # Current + 1
			Result.front ~ Current
			Result.last ~ v
		end

	prepended alias "|<-" (v: G): like Current
			-- Return a sequence representing current with 'v' added to beginning
		do
			Result := Current.deep_twin
			Result.prepend (v)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_incremented:
				# Result = # Current + 1
			Result.first ~ v
			Result.tail ~ Current
		end

	subsequenced (i, j: INTEGER): like Current
			-- Segment of sequence i..j
		require
			valid_position (i)
			valid_position (j)
		do
			Result := Current.deep_twin
			Result.subsequence (i, j)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			j >= i IMPLIES # Result = j - i + 1
			j <  i IMPLIES # Result = 0
			across
				i |..| j as pos
			all
				Current[pos.item] ~ Result[pos.item - i + 1]
			end
		end

	concatenated alias "|++|" (other: like Current): like Current
			-- Return a sequence representing current with 'other' appended
		do
			Result := Current.deep_twin
			Result.concatenate (other)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_incremented:
				# Result = # Current + # other
			across 1 |..| (# Current + # other) as pos all
				pos.item <= # Current IMPLIES
					Result[pos.item] ~ Current[pos.item]
				AND
				pos.item > # Current IMPLIES
					Result[pos.item] ~ other[pos.item - # Current]
			end
		end

	overriden (v: G; i: INTEGER): like Current
		require
			valid_position (i)
		do
			Result := Current.deep_twin
			Result.override (v, i)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_incremented:
				# Current = # Result
			across 1 |..| count as pos all
				pos.item = i IMPLIES
					Result[pos.item] ~ v
				AND
				pos.item /= i IMPLIES
					Result[pos.item] ~ Current[pos.item]
			end
		end

	inserted (v: G; i: INTEGER): like Current
			-- Return a new sequence representing current with
			-- `v' inserted as the `i'-th entry, if in index interval
		require
			valid_position (i)
		do
			Result := Current.deep_twin
			Result.insert (v, i)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_incremented:
				# Result = # Current + 1
			Result ~
				subsequenced (1, i - 1).appended (v) |++| subsequenced (i, count)
		end

	removed (i: INTEGER): like Current
			-- Return a new sequence representing current with
			-- `i'-th entry, if in index interval, removed
		require
			valid_position (i)
		do
			Result := Current.deep_twin
			Result.remove (i)
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			count_decremented:
				# Result = # Current - 1
			Result ~ subsequenced (1, i - 1) |++| subsequenced (i + 1, count)
		end

	reversed: like Current
			-- Return an reversed version of current sequence
		do
			Result := Current.deep_twin
			Result.reverse
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			same_count:
				# Current = # Result
			reverse_property_1:
				Current ~ Result.reversed
			reverse_property_2:
				across 1 |..| count as i all
					Current[i.item] ~ Result[count - i.item + 1]
				end
		end

		slice(a_start,a_end,a_step: INTEGER): like Current
			require
				lower <= a_start and a_start <= a_end and a_end <= upper
				a_step >= 0
			local
				i: INTEGER
			do
				create Result.make_empty
				from
					i := a_start
				until
					i > a_end
				loop
					Result.append (item (i))
					i := i + a_step
				end
			end

feature -- Quantification

	hold_count (exp: PREDICATE [PAIR[INTEGER, G]]): INTEGER
			-- How many items satisfying `exp' are in `Current'?
		local
			i: INTEGER
			p: PAIR[INTEGER, G]
		do
			i := 1
			across
				Current as c
			loop
				create p.make (i, c.item)
				if exp.item ([p]) then
					Result := Result + 1
				end
				i := i + 1
			end
		ensure
			current_seq_unchanged:
				Current ~ old Current.deep_twin
			maximum_result: Result <= count
		end

	comprehension alias "|" (exp: PREDICATE [PAIR[INTEGER, G]]): like Current
			-- Form elements of current sequence that satisfy `exp'
			-- as a new sequence
		local
			i: INTEGER
			p: PAIR[INTEGER, G]
		do
			create Result.make_empty
			i := 1
			across
				Current as c
			loop
				create p.make (i, c.item)
				if exp.item ([p]) then
					Result.append (c.item)
				end
				i := i + 1
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			all_satisfying_items_exist:
				across Result as cur all
					Current.has (cur.item)
				end
			all_satisfying_exp:
				Result.hold_count (exp) = # Result
			consistent_satisfying_items:
				Current.hold_count (exp) = # Result
		end

feature -- Equality

	is_equal(other: like Current): BOOLEAN
			-- Is current sequence equal to `other'?
		do
			Result := imp ~ other.imp
		ensure then
			Result = (as_function ~ other.as_function)
		end

feature -- Output

	out: STRING
			-- Return string representation of current sequence.
		local
			i: INTEGER
		do
			create Result.make_empty
			Result.append ("< ")
			from
				i := 1
			until
				i > count
			loop
				check attached {G} imp.i_th(i) as e then
					Result.append (e.out)
				end
				if i < count then
					Result.append (", ")
				end
				i := i + 1
			end
			Result.append (" >")
		end

	debug_output: STRING
			-- Return string representation of current sequence for debugging
		do
			Result := out
		end

feature -- Conversion

	as_array : ARRAY[G]
			-- Return current sequence as an array
		do
			create Result.make_empty
			across
				Current as cur
			loop
				Result.force (cur.item, Result.upper + 1)
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			Result.lower = 1
			Result.upper = count
			across 1 |..| count as pos all
				Current[pos.item] ~ Result[pos.item]
			end
		end

	as_function: FUN[INTEGER, G]
			-- Return current sequence as a function
			-- with its domain being the set of positions
		local
			i: INTEGER
			pair: PAIR[INTEGER, G]
		do
			create Result.make_empty
			i := 1
			across
				Current as cur
			loop
				create pair.make (i, cur.item)
				Result.extend (pair)
				i := i + 1
			end
		ensure
			current_set_unchanged:
				Current ~ old Current.deep_twin
			all_positions_included:
				# Result.domain = # Current
			across Result.domain as pos all
				valid_position (pos.item)
			end
			across Result.domain as pos all
				Current[pos.item] ~ Result[pos.item]
			end
		end

feature -- Auxiliary functions for contracts

	valid_position (pos: INTEGER): BOOLEAN
			-- Is 'pos' a valid position in current sequence
		do
			Result := 1 <= pos and then pos <= count
		ensure
			Result = (1 <= pos and pos <= # Current)
		end

feature {SEQ} -- Auxiliary functions for checking subsequences

	is_augmented_subseq_of (s1, s2: SEQ[TUPLE[g: G; i: INTEGER]]): BOOLEAN
			-- Given that both 's1' and 's2' are augmented sequences,
			-- is 's1' a contiguous subsequence of 's2'?
			-- e.g., <<[a, 1], [b, 2]>> is a contiguous subsequence of
			--       <<[a, 3], [b, 3]>>
		local
			i: INTEGER
		do
			if s1.is_empty then
				Result := TRUE
			else
				from
					Result := FALSE
					i := 1
				until
					-- it's been found that Current is a subseq of 'other'
					Result OR ELSE
						-- s1 is longer than the remaining part of s2
						s2.count - i + 1 < s1.count
				loop
					if s1[1].g ~ s2[i].g then
					-- subsequence may start with 'i' in s2
						Result :=
							across i |..| (i + s1.count - 1) as j all
								s1[j.item - i.item + 1].g ~ s2[j.item].g and then
								s1[j.item - i.item + 1].i <= s2[j.item].i
							end
					else
						-- subsequence cannot start with 'i' in s2
						-- do nothing and proceed to increment 'i'
					end
					i := i + 1
				end
			end
		end

	augmented_with_collapsed_rep: SEQ[TUPLE[g: G; i:INTEGER]]
			-- e.g., <<a, b, b, c, d>> augmented to
			-- <<[a, 1], [b, 2], [c, 1], [d, 1]>>
		local
			i: INTEGER
			element: G
		do
			create Result.make_empty
			from
				i := 1
				imp.start
			until
				imp.after
			loop
				element := imp.item
				if i > 1 then
					if imp[i - 1] ~ element then
						Result[Result.count] := [Result.last.g, Result.last.i + 1]
					else
						Result.append ([element, 1])
					end
				else
					Result.append ([element, 1])
				end
				i := i + 1
				imp.forth
			end
		end

	augmented_without_collapsed_rep: SEQ[TUPLE[G, INTEGER]]
			-- e.g., <<a, b, b, c, d>> augmented to
			-- <<[a, 1], [b, 1], [b, 1], [c, 1], [d, 1]>>
		do
			create Result.make_empty
			across
				Current as cur
			loop
				Result.append ([cur.item, 1])
			end
		end

feature{SEQ} -- Implementation

	imp: ARRAYED_LIST[G]

	set_imp (new_imp: like imp)
		do
			imp := new_imp
		ensure
			imp = new_imp
		end

invariant

	value_semantics:
		imp.object_comparison

	lower = 1
	imp.lower = lower
	is_empty = (upper < lower)

	properties:
		not is_empty implies
			Current ~ tail.prepended (first)
			and
			Current ~ front.appended (last)
end
