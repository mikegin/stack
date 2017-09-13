note
	description: "Pairs."
	author: "Jackie Wang"

class
	PAIR[G -> attached ANY, H -> attached ANy]
inherit
	ANY
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
	make,
	make_from_tuple

-- commented out due to an unresolved issue:
--  https://www2.eiffel.com/support/protected/report.aspx?pr=19050
-- this is now supposedly fixed
convert
    make_from_tuple ({TUPLE[G, H]}),
    as_tuple: {TUPLE[G,H]}

feature -- Queries

	first: G

	second: H

feature -- Constructor

	make (g: G; h: H)
		do
			first := g
			second := h
		end

	make_from_tuple (t: TUPLE[g: G; h: H])
		require
			t.count = 2
			attached {G} t.g
			attached {H} t.h
		do
			make (t.g, t.h)
		end

	as_tuple: TUPLE[G, H]
		do
			Result := [first, second]
			Result.compare_objects
		end

feature -- Equality

	is_equal (other: like Current): BOOLEAN
			-- Is current pair equal to 'other'?
		do
			Result := first ~ other.first and then
						second ~ other.second
		end

feature -- Debug output

	debug_output: STRING
		do
			Result := out
		end

	out: STRING
		do
			create Result.make_empty
			check attached {G} first  as fst then
			check attached {H} second as snd then
				Result.append (fst.out)
				Result.append (" -> ")
				Result.append (snd.out)
			end
			end
		end
end
