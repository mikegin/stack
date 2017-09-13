note
	description: "[
			Floating point numbers based on REAL_64
			With an approximately equal operator,
			see FLOAT_COMPARABLE
		]"
	author: ""
	date: "$Date$"
	revision: "$Revision$"

expanded class
	FLOAT
inherit
	REAL_64_REF

create
	default_create,
	make_from_reference,
	make_from_real,
	make_from_integer_32

convert
	make_from_reference ({REAL_64_REF}),
	make_from_real({REAL_64}),
	make_from_integer_32 ({INTEGER_32}),
	as_real: {REAL_64}

feature
	make_from_real(r: REAL_64)
		do
			make_from_reference (r)
		end

	make_from_integer_32 (x: INTEGER_32)
		do
			make_from_real (x)
		end

feature -- Equality

	is_approx_equal alias "|~|" (x: FLOAT): FLOAT_COMPARER
		do
			create Result.make (Current, x)
		end

feature -- Conversion

	as_real: REAL_64
		do
			Result := item
		end

feature -- formatting


	formatted(n:INTEGER): STRING
		local
			format: FORMAT_DOUBLE
		do
			create format.make (16,n)
			format.no_justify
			Result := format.formatted (Current)
		end
end
