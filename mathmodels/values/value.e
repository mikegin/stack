note
	description: "[
		Perform arithmetic (+, -, *, /) on real numbers of arbitrary precision.
		In the case of division, the default precision is 35 digits after
		the decimal point. This can be changed via `set_division_precision'.
		The queries `is_integer', `is_natural` and `is_natural1' may be used to
		check that the value is an integer or natural number. 
		`out' provides a string represesentation rounded to two decimal places, and 
		`precise_out' is a string representation of the precise value. The corresponding
		C# class was the inspiration for this class.
		]"
	author: "Vlad Gerchikov for the Software Engineering Lab at sel@cse.yorku.ca"
	date: "$April 15, 2008$"
	revision: "$1.0$"

expanded class
	VALUE
inherit
	COMPARABLE
		redefine is_equal, default_create, out end
	NUMERIC
		redefine is_equal, default_create, out end

create
	make_from_string, make, make_from_int, default_create

convert
	make_from_string ({STRING}),
	as_double: {REAL_64}

feature {VALUE} -- private fields	
	s_: STRING
	divisionDecimalPrecision_: INTEGER -- the minimum accuracy of division results; division results will be accurate to AT LEAST this many digits
	default_precision: INTEGER = 35

	make (s: STRING; dv: INTEGER)
		-- create a MONEY_VALUE object from string `s'
	require
		non_void: s /= void
		non_empty: not s.is_empty
		has_correct_format: ensureValid(s)
	do
		divisiondecimalprecision_ := dv
		s_ := s
	end


	clone_me: VALUE
	local
		l_s: STRING
	do
		create l_s.make_from_string (s_)
--		l_s := s_.out.twin
		create Result.make (l_s, divisiondecimalprecision_)
--		create Result.make (l_s, divisiondecimalprecision_)
	end

feature {NONE} -- constructors
	default_create
			-- create an empty MONEY_VALUE object (it's equivalent to 0)
		local
			empty: STRING
		do
			divisiondecimalprecision_ := default_precision
			empty := "0"
			s_ := empty.twin

		ensure then
			s_.is_equal ("0")
		end

	make_from_string (s: STRING)
		-- create a MONEY_VALUE object from string `s'
	require
		non_void: s /= void
		non_empty: not s.is_empty
		has_correct_format: ensureValid(s)
	do
		divisiondecimalprecision_ := default_precision
		s_ := s.twin
		normalize

	end

	make_from_int (int: INTEGER)
		-- create a MONEY_VALUE object from integer `m'
	local
		ch: CHARACTER
		m, n, d: INTEGER
		neg: BOOLEAN
	do
		divisiondecimalprecision_ := default_precision
		m := int

		if m = 0 then
			create s_.make_from_string ("0")
		else
			neg := m < 0
			if neg then
				m := m * -1
			end

			from
				n := m
				create s_.make_empty
			until
				n = 0
			loop
				d := n \\ 10;
				n := n // 10;

				ch := toChar(d)
				s_.insert_character (ch, 1)
			end

			if neg then
				negate
			end

			normalize
		end
	end





feature -- comparison
	is_equal (other: VALUE): BOOLEAN
			-- check whether other is equal to current or not
		local
			r1i, r2i, d1, d2: INTEGER
			r1, r2: VALUE
		do
			r1 := current.clone_me
			r2 := other.clone_me

			r1.alignDecimal(r2)
			r1.alignWhole(r2)

			result := true

			from
				r1i := 1
				r2i := 1
			until
				r1i > r1.s_.count or r2i > r2.s_.count
			loop
				d1 := toDigit(r1.s_.item (r1i))
				d2 := toDigit(r2.s_.item (r2i))

				if d1 /= d2 then
					result := false
					r1i := r1.s_.count + 1 -- stop looping
				end

				r1i := r1i + 1
				r2i := r2i + 1
			end
		end

	is_less alias "<" (other: VALUE): BOOLEAN
			-- whether current is less than other
		local
			r1i, r2i, d1, d2: INTEGER
			r1, r2: VALUE
		do
			r1 := current.clone_me
			r2 := other.clone_me

			if r1.s_.item (1) = '-' and r2.s_.item (1) /= '-' then
				result := true
			elseif r1.s_.item (1) /= '-' and r2.s_.item (1) = '-' then
				result := false
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) = '-' then
				r1.negate
				r2.negate
				result := r2 < r1
			else
				r1.alignDecimal(r2)
				r1.alignWhole(r2)

				result := false

				from
					r1i := 1
					r2i := 1
				until
					r1i > r1.s_.count or r2i > r2.s_.count
				loop
					d1 := toDigit(r1.s_.item (r1i))
					d2 := toDigit(r2.s_.item (r2i))

					if d1 < d2 then
						result := true
						r1i := r1.s_.count + 1 -- stop looping
					elseif d1 > d2 then
						result := false
						r1i := r1.s_.count + 1 -- stop looping
					end

					r1i := r1i + 1
					r2i := r2i + 1
				end
			end
		end

feature -- operations
	plus alias "+", add (other: VALUE): VALUE
			-- adds current to other and returns a new object
		local
			res, empty: STRING
			carry, r1i, r2i, d1, d2, d: INTEGER
			ch : CHARACTER
			r1, r2: VALUE
		do
			r1 := current.clone_me
			r2 := other.clone_me

			if r1.s_.item (1) = '-' and r2.s_.item (1) /= '-' then
				create result
				r1.negate
				result := (r2 - r1).clone_me
			elseif r1.s_.item (1) /= '-' and r2.s_.item (1) = '-' then
				create result
				r2.negate
				result := (r1 - r2).clone_me
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) = '-' then
				create result
				r1.negate
				r2.negate
				result := (r1 + r2).clone_me
				result.negate
			else
				r1.alignDecimal(r2)
				r1.alignWhole(r2)

				empty := ""
				res := empty.twin

				from
					r1i := r1.s_.count
					r2i := r2.s_.count
				until
					r1i < 1 or r2i < 1
				loop
					ch := '0'

					if r1.s_.item (r1i) /= '.' and r2.s_.item (r2i) /= '.' then
						d1 := toDigit(r1.s_.item (r1i))
						d2 := toDigit(r2.s_.item (r2i))
						d := carry + d1 + d2

						if d >= 10 then
							carry := d // 10
							d := d - 10
						else
							carry := 0
						end

						ch := toChar(d)
					elseif r1.s_.item (r1i) = '.' and r2.s_.item (r2i) = '.' then
						ch := '.'
					end

					res.insert_character (ch, 1)

					r1i := r1i - 1
					r2i := r2i - 1
				end

				if carry > 0 then
					res.insert_character (toChar(carry), 1)
				end

				create result.make_from_string(res)
			end
		end

	minus alias "-", subtract (other: VALUE): VALUE
			-- subtracts other from current and returns a new object
		local
			res, empty: STRING
			r1, r2: VALUE
			r1i, r2i, d1, d2, dp, i, j: INTEGER
			ch: CHARACTER
		do
			r1 := current.clone_me
			r2 := other.clone_me

			if r1.s_.item (1) = '-' and r2.s_.item (1) /= '-' then
				create result
				r1.negate
				result := (r1 + r2).clone_me
				result.negate
			elseif r1.s_.item (1) /= '-' and r2.s_.item (1) = '-' then
				create result
				r2.negate
				result := (r1 + r2).clone_me
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) = '-' then
				create result
				r2.negate
				result := (r1 + r2).clone_me
			else
				-- ensure r1 >= r2
				if r1 < r2 then
					result := (r2 - r1).clone_me
					result.negate
				else
					r1.alignDecimal(r2)
					r1.alignWhole(r2)

					empty := ""
					res := empty.twin

					from
						r1i := r1.s_.count
						r2i := r2.s_.count
					until
						r1i < 1 or r2i < 1
					loop
						ch := '0'

						if r1.s_.item (r1i) /= '.' and r2.s_.item (r2i) /= '.' then
							d1 := toDigit(r1.s_.item (r1i))
							d2 := toDigit(r2.s_.item (r2i))

							-- do we need to borrow?
							if d1 < d2 then
								from
									i := r1i - 1
								until
									i < 1
								loop
									if r1.s_.item (i) /= '.' then
										dp := toDigit(r1.s_.item (i))

										if dp > 0 then
											r1.s_.put (toChar(dp - 1), i)

											from
												j := i + 1
											until
												j > r1i - 1
											loop
												if r1.s_.item (j) /= '.' then
													r1.s_.put (toChar(toDigit(r1.s_.item (j)) + 9), j)
												end

												j := j + 1
											end

											d1 := d1 + 10
											i := 0 -- stop looping
										end
									end

									i := i - 1
								end
							end

							ch := toChar(d1 - d2)
						elseif r1.s_.item (r1i) = '.' and r2.s_.item (r2i) = '.' then
							ch := '.'
						end

						res.insert_character (ch, 1)

						r1i := r1i - 1
						r2i := r2i - 1
					end

					create result.make_from_string(res)
				end
			end
		end

	product alias "*", multiply (other: VALUE): VALUE
			-- multiplies current by other and returns a new object
		local
			r1, r2, tr1, tr2, tr: VALUE
			r1DotPos, r2DotPos, precision, r1i, r2i, carry, d1, d2, d, diff, i: INTEGER
			res, cRes, tmp, empty: STRING
		do
			r1 := current.clone_me
			r2 := other.clone_me

			if r1.s_.item (1) = '-' and r2.s_.item (1) /= '-' then
				create result
				r1.negate
				result := (r1 * r2).clone_me
				result.negate
			elseif r1.s_.item (1) /= '-' and r2.s_.item (1) = '-' then
				create result
				r2.negate
				result := (r1 * r2).clone_me
				result.negate
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) = '-' then
				create result
				r1.negate
				r2.negate
				result := (r1 * r2).clone_me
			else
				-- remove decimal points, if any, and remember the sum of the number of digits after the decimal for both numbers
				r1DotPos := r1.s_.index_of ('.', 1)
				r2DotPos := r2.s_.index_of ('.', 1)
				precision := 0

				if r1DotPos > 0 then
					precision := precision + r1.s_.count - r1DotPos
					r1.s_.remove (r1DotPos)
				end
				if r2DotPos > 0 then
					precision := precision + r2.s_.count - r2DotPos
					r2.s_.remove (r2DotPos)
				end

				-- perform the actual multiplication
				empty := ""
				res := empty.twin

				from
					r2i := r2.s_.count
				until
					r2i < 1
				loop
					cRes := empty.twin
					carry := 0

					from
						r1i := r1.s_.count
					until
						r1i < 1
					loop
						d1 := toDigit(r1.s_.item (r1i))
						d2 := toDigit(r2.s_.item (r2i))
						d := carry + d1 * d2;

						if d >= 10 then
							carry := d // 10
							d := d \\ 10
						else
							carry := 0
						end

						cRes.insert_character (toChar(d), 1)

						r1i := r1i - 1
					end

					if carry > 0 then
						cRes.insert_character (toChar(carry), 1)
					end

					if res.count = 0 then
						res := cRes.twin
					else
						create tmp.make_filled ('0', r2.s_.count - r2i)
						cRes.append (tmp)
						create tr1.make_from_string (cRes)
						create tr2.make_from_string (res)
						tr := tr1 + tr2
						res := tr.s_.twin
					end

					r2i := r2i - 1
				end

				-- put back the decimal point
				if precision > 0 then
					if precision > res.count then
						diff := precision - res.count
						from
							i := 1
						until
							i > diff
						loop
							res.insert_character ('0', 1)

							i := i + 1
						end
					end

					res.insert_character ('.', res.count - precision + 1)
				end

				create result.make_from_string(res)
			end
		end

	quotient alias  "/", divide (other: VALUE): VALUE
			-- divides current by other and returns a new object
		local
			r1, r2, tr, diff, x, sum, prod: VALUE
			r1DotPos, r2DotPos, r1Precision, r2Precision, r1NumTrailingZeros, r2NumTrailingZeros, scaleFactor, i, startPos, r1i, d: INTEGER
			s, res, empty: STRING
			pad: detachable STRING
			stopLoop: BOOLEAN
			ch: CHARACTER
		do
			r1 := current.clone_me
			r2 := other.clone_me

			if r1.is_equal (zero) then
				result := zero
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) /= '-' then
				create result
				r1.negate
				result := (r1 / r2).clone_me
				result.negate
			elseif r1.s_.item (1) /= '-' and r2.s_.item (1) = '-' then
				create result
				r2.negate
				result := (r1 / r2).clone_me
				result.negate
			elseif r1.s_.item (1) = '-' and r2.s_.item (1) = '-' then
				create result
				r1.negate
				r2.negate
				result := (r1 / r2).clone_me
			else
				-- remove decimal points by scaling both r1 and r2
				r1DotPos := r1.s_.index_of ('.', 1)
				r2DotPos := r2.s_.index_of ('.', 1)
				r1Precision := 0
				r2Precision := 0

				if r1DotPos > 0 then
					r1Precision := r1.s_.count - r1DotPos;
					r1.s_.remove (r1DotPos)
					r1.normalize
				end
				if r2DotPos > 0 then
					r2Precision := r2.s_.count - r2DotPos;
					r2.s_.remove (r2DotPos)
					r2.normalize
				end
				pad := void
				if r1Precision > r2Precision then
					pad := r2.s_
				elseif r2Precision > r1Precision then
					pad := r1.s_
				end
				if pad /= void then
					create s.make_filled ('0', (r1Precision - r2Precision).abs)
					pad.append (s)
				end

				-- adjust r1 to produce the required precision, if necessary
				r1NumTrailingZeros := 0
				r2NumTrailingZeros := 0
				scaleFactor := 0

				from
					i := r1.s_.count
				until
					i < 1
				loop
					if r1.s_.item (i) = '0' then
						r1NumTrailingZeros := r1NumTrailingZeros + 1
					else
						i := 0 -- stop looping
					end

					i := i - 1
				end

				from
					i := r2.s_.count
				until
					i < 1
				loop
					if r2.s_.item (i) = '0' then
						r2NumTrailingZeros := r2NumTrailingZeros + 1
					else
						i := 0 -- stop looping
					end

					i := i - 1
				end

				if r1NumTrailingZeros < r2NumTrailingZeros then
					create s.make_filled ('0', r2NumTrailingZeros - r1NumTrailingZeros)
					r1.s_.append (s)
					scaleFactor := scaleFactor + r2NumTrailingZeros - r1NumTrailingZeros
					r1NumTrailingZeros := r2NumTrailingZeros
				end
				if r1NumTrailingZeros - r2NumTrailingZeros < divisionDecimalPrecision_ + 1 then
					scaleFactor := scaleFactor + divisionDecimalPrecision_ + 1 - (r1NumTrailingZeros - r2NumTrailingZeros);
					create s.make_filled ('0', divisionDecimalPrecision_ + 1 - (r1NumTrailingZeros - r2NumTrailingZeros))
					r1.s_.append (s)
				end

				-- ensure r1 >= r2; if this is not the case, multiply r1 by a sufficient power of 10, and then at the end divide by the same power
				if r1 < r2 then
					scaleFactor := scaleFactor + r2.s_.count - r1.s_.count + 1;
					create s.make_filled ('0', r2.s_.count - r1.s_.count + 1)
					r1.s_.append (s)
				end

				if r1.s_.count - r2.s_.count < divisionDecimalPrecision_ then
					scaleFactor := scaleFactor + divisionDecimalPrecision_ - (r1.s_.count - r2.s_.count)
					create s.make_filled ('0', divisionDecimalPrecision_ - (r1.s_.count - r2.s_.count))
					r1.s_.append (s)
				end

				-- perform actual division (long division)
				startPos := r2.s_.count + 1
				if r1.s_.count > r2.s_.count then
					from
						stopLoop := false
					until
						startPos > r1.s_.count or stopLoop
					loop
						s := r1.s_.substring(1, startPos - 1)
						create tr.make_from_string (s)
						if tr >= r2 then
							stopLoop := true
						else
							startPos := startPos + 1
						end
					end
				end

				empty := ""
				res := empty.twin
				create diff
				from
					r1i := startPos - 1
				until
					r1i > r1.s_.count
				loop
					if r1i = startPos - 1 then
						create x.make_from_string (r1.s_.substring(1, r1i))
					else
						diff.s_.insert_character (r1.s_.item (r1i), diff.s_.count + 1)
						create x
						x := diff.clone_me
					end

					d := 0
					create sum
					from
						stopLoop := false
					until
						stopLoop
					loop -- executes at most 9 times
						sum := sum + r2
						if sum > x then
							stopLoop := true
						else
							d := d + 1
						end
					end

					ch := toChar(d)
					res.insert_character (ch, res.count + 1)

					create prod
					create s.make_filled (ch, 1)
					create tr.make_from_string (s)
					prod := tr * r2
					diff := x - prod

					r1i := r1i + 1
				end

				-- put back the decimal point
				if scaleFactor > 0 then
					if scaleFactor > res.count then
						create s.make_filled ('0', scaleFactor - res.count)
						res.insert_string (s, 1)
					end

					res.insert_character ('.', res.count - scaleFactor + 1)
				end

				create result.make_from_string(res)
			end
		end

	opposite alias "-": VALUE
		-- unary minus
		do
			create result.make_from_string (s_)
			result.negate
		end

	identity alias "+": VALUE
		-- unary plus
		do
			create result.make_from_string (s_)
		end

	zero: VALUE
		-- neutral element for "+" and "-"
		do
			create result.make_from_string ("0")
		end

	one: VALUE
		-- neutral element for "*" and "/"
		do
			create result.make_from_string ("1")
		end

	divisible (other: VALUE): BOOLEAN
		-- may current object be divided by `other'?
		do
			result := not other.is_equal (zero)
		end

	exponentiable (other: NUMERIC): BOOLEAN
		-- may current object be elevated to the power `other'?
		do
			result := false
		end

	is_natural: BOOLEAN
		do
			result := is_integer and current >= zero
		end

	is_natural1: BOOLEAN
		do
			result := is_integer and current >= one
		end

	is_integer: BOOLEAN
		do
			result := s_.index_of ('.', 1) = 0
		end

	set_division_precision (i: INTEGER)
			-- sets divisionDecimalPrecision_ to 'i'
		require
			greater_than_zero: i > 0
		do
			divisionDecimalPrecision_ := i
		end

feature -- Conversion
	as_double: REAL_64
			-- represent as a DOUBLE
		do
			Result := precise_out.to_double
		end

feature -- printing
	precise_out: STRING
		-- what is the string representation of VALUE_IMP
	do
		result := s_.twin
	end

	out: STRING
		-- return a representation of the number rounded to two decimal places
	local
		myClone: VALUE
		precision, missingZeros, idxDot, roundDigits: INTEGER
		pad: STRING
	do
		myClone := current.clone_me
		roundDigits := 2
		myClone.round (roundDigits)

		idxDot := myClone.s_.index_of ('.', 1)
		if idxDot = 0 then
			myClone.s_.append_character ('.')
			create pad.make_filled ('0', roundDigits)
			myClone.s_.append_string (pad)
		else
			precision := myClone.s_.count - idxDot
			missingZeros := roundDigits - precision

			if missingZeros > 0 then
				create pad.make_filled ('0', missingZeros)
				myClone.s_.append_string (pad)
			end
		end

		result := myClone.s_.twin
	end

feature {ANY} -- rounding

	round_to (digits: INTEGER): VALUE
			-- rounds the current VALUE_IMP to 'digits'
			-- symmetric rounding as in Excel http://support.microsoft.com/kb/196652
			-- -2.6 is rounded to -3
		require
			digits >= 0
		do
			Result := Current.clone_me
			Result.round (digits)
		end

	precise_out_to (digits: INTEGER): STRING
			-- returns the precise string representation to 'digits'
		require
			digits >= 0
		local
			dotPos: INTEGER
		do
			Result := precise_out
			dotPos := Result.index_of ('.', 1)
			if dotPos > 0 then
				Result := Result.substring(1, dotPos + digits)
			end
		end

	round (digits: INTEGER)
			-- rounds this instance to the specified number of digits
		require
			digits >= 0
		local
			dotPos: INTEGER
			neg: BOOLEAN
			s, tmp: STRING
			x, y: VALUE
		do
			dotPos := s_.index_of ('.', 1)
			if dotPos > 0 then
				neg := false
				if s_.item (1) = '-' then
					negate
					neg := true
				end

				create s.make_filled ('0', digits)
				s.append ("5")
				s.insert_string ("0.", 1)
				create x.make_from_string (s)
				y := current + x
				dotPos := y.s_.index_of ('.', 1)
				tmp := y.s_.substring(1, dotPos + digits)
				s_ := tmp.twin

				if neg then
					negate
				end
			end

			normalize
		end

	negate
		-- negates the number
		local
			tmp: STRING
		do
			if s_.item (1) = '-' then
				tmp := s_.substring(2, s_.count)
				s_ := tmp.twin
			else
				s_.insert_character ('-', 1)
			end
		end

	epsilon_singleton: VALUE_SINGLETON
		once
			create Result
		end

	set_epsilon (v: STRING)
		do
			epsilon_singleton.set_epsilon (v)
		ensure

		end

	is_imprecise_equal alias "|~" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current = other
			else
				Result := (Current-other).absolute <= epsilon_singleton.epsilon
			end
		end

	is_imprecise_equal_negation alias "|/~" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current /= other
			else
				Result := not(Current |~ other)
			end
		end

	is_imprecise_less alias "|<" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current < other
			else
				Result := Current < (other - epsilon_singleton.epsilon)
			end
		end

	is_imprecise_less_equal alias "|<~" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current <= other
			else
				Result := (Current |~ other) or (Current < (other - epsilon_singleton.epsilon))
			end
		end

	is_imprecise_greater alias "|>" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current > other
			else
				Result := Current > (other + epsilon_singleton.epsilon)
			end
		end


	is_imprecise_greater_equal alias "|>~" (other: VALUE): BOOLEAN
		do
			If epsilon_singleton.epsilon = "0.0" then
				Result := Current >= other
			else
				Result := (Current |~ other) or (Current > (other + epsilon_singleton.epsilon))
			end
		end

	absolute: VALUE
			do
				if Current >= Current.zero then
					Result := Current.clone_me
				else
					Result := opposite.clone_me
				end
			ensure
				Result >= Result.zero
			end

feature {VALUE} -- private methods
	ensureValid (s: STRING): BOOLEAN
		-- check if the given string is of the correct format
		require
			non_void: s /= void
			non_empty: not s.is_empty
		local
			seenDot: BOOLEAN
			i: INTEGER
		do
			-- valid patterns are: [-]?[0-9]+.[0-9]+ or .[0-9]+ or [-]?[0-9]+

			seenDot := false
			result := true

			from
				i := 1
			until
				i > s.count
			loop
				if s.item (i) = '-' then
					if i > 1 then
						result := false
						i := s.count + 1 -- stop looping
					end
				elseif s.item (i) = '.' then
					if i = s.count or seenDot then
						result := false
						i := s.count + 1 -- stop looping
					end

					seenDot := true
				elseif not s.item (i).is_digit then
					result := false
					i := s.count + 1 -- stop looping
				end

				i := i + 1
			end
		end

	normalize
		-- standardizes the format of the real number
		require
			non_empty: not s_.is_empty
		local
			i, insPos, dotPos, firstNonZeroPos, lastNonZeroPos: INTEGER
			seenMinus, prependZero, hasDot: BOOLEAN
			whole, fraction, empty, tmp, zeroStr: STRING
		do
			empty := ""
			zeroStr := "0"
			seenMinus := false
			prependZero := false

			from
				i := 1
			until
				i > s_.count
			loop
				if s_.item (i) = '-' then
					seenMinus := true
				elseif s_.item (i) = '.' then
					if i = 1 or seenMinus then
						prependZero := true
					end
				end

				i := i + 1
			end

			if prependZero then
				insPos := 1
				if seenMinus then
					insPos := 2
				end
				s_.insert_character ('0', insPos)
			end

			if (seenMinus) then
				negate
			end

			dotPos := s_.index_of ('.', 1)
			if dotPos = 0 then -- no '.' in the string
				hasDot := false
				whole := s_.twin
				fraction := empty.twin
			else -- '.' exists in the string
				hasDot := true
				tmp := s_.substring(1, dotPos - 1)
				whole := tmp.twin
				tmp := s_.substring(dotPos + 1, s_.count)
				fraction := tmp.twin
			end

			if not whole.is_empty then
				firstNonZeroPos := whole.count + 1
				from
					i := 1
				until
					i > whole.count
				loop
					if whole.item (i) /= '0' then
						firstNonZeroPos := i
						i := whole.count + 1 -- stop looping
					end

					i := i + 1
				end

				if firstNonZeroPos = whole.count + 1 then
					whole := zeroStr.twin
				else
					tmp := whole.substring(firstNonZeroPos, whole.count)
					whole := tmp.twin
				end
			end
			if not fraction.is_empty then
				lastNonZeroPos := -1
				from
					i := fraction.count
				until
					i < 1
				loop
					if fraction.item (i) /= '0' then
						lastNonZeroPos := i
						i := 0 -- stop looping
					end

					i := i - 1
				end

				if lastNonZeroPos = -1 then
					fraction := empty.twin
				else
					tmp := fraction.substring(1, lastNonZeroPos)
					fraction := tmp.twin
				end
			end

			s_ := whole.twin
			if hasDot and not fraction.is_empty then
				s_.append (".")
				s_.append (fraction)
			end

			if seenMinus and not s_.is_equal ("0") then
				s_.insert_character ('-', 1)
			end
		end

		toDigit(ch: CHARACTER) : INTEGER
			-- converts a character to a digit
			local
				chZero: CHARACTER
			do
				chZero := '0'
				result := ch.code - chZero.code
			end

		toChar(d: INTEGER) : CHARACTER
			-- converts a digit to a character
			local
				chZero: CHARACTER
			do
				chZero := '0'
				result := (chZero.code + d).to_character_8
			end

		alignDecimal (other: VALUE)
			-- used to align the fractional parts of the given parameters
			local
				myDotPos, otherDotPos, myPrec, otherPrec, numToPad, i: INTEGER
				pad: detachable STRING
			do
				myDotPos := s_.index_of ('.', 1)
				otherDotPos := other.s_.index_of('.', 1)

				if myDotPos /= 0 and otherDotPos /= 0 then
					myPrec := s_.count - myDotPos
					otherPrec := other.s_.count - otherDotPos

					if myPrec /= otherPrec then
						pad := void

						if myPrec < otherPrec then
							pad := s_
						else
							pad := other.s_
						end

						numToPad := (myPrec - otherPrec).abs
						from
							i := 1
						until
							i > numToPad
						loop
							pad.append_character ('0')

							i := i + 1
						end
					end
				elseif myDotPos /= 0 or otherDotPos /= 0 then
					if myDotPos /= 0 then
						myPrec := s_.count - myDotPos
					else
						myPrec := 0
					end
					if otherDotPos /= 0 then
						otherPrec := other.s_.count - otherDotPos
					else
						otherPrec := 0
					end

					pad := void
					if myPrec < otherPrec then
						pad := s_
					else
						pad := other.s_
					end

					numToPad := (myPrec - otherPrec).abs
					pad.append_character ('.')
					from
						i := 1
					until
						i > numToPad
					loop
						pad.append_character ('0')

						i := i + 1
					end
				end
			end

		alignWhole (other: VALUE)
			-- used to align the integer parts of the given parameters
			local
				myDotPos, otherDotPos, myWholeLength, otherWholeLength, meNegOffset, otherNegOffset, insPos, numToPad, i: INTEGER
				meNeg, otherNeg: BOOLEAN
				pad: detachable STRING
			do
				myDotPos := s_.index_of('.', 1)
				otherDotPos := other.s_.index_of('.', 1)

				meNeg := s_.item (1) = '-'
				otherNeg := other.s_.item (1) = '-'

				if myDotPos /= 0 then
					if meNeg then
						meNegOffset := 1
					else
						meNegOffset := 0
					end
					myWholeLength := myDotPos - meNegOffset - 1
				else
					myWholeLength := s_.count
				end
				if otherDotPos /= 0 then
					if otherNeg then
						otherNegOffset := 1
					else
						otherNegOffset := 0
					end
					otherWholeLength := otherDotPos - otherNegOffset - 1
				else
					otherWholeLength := other.s_.count
				end

				if myWholeLength /= otherWholeLength then
					pad := void
					if myWholeLength < otherWholeLength then
						pad := s_
					else
						pad := other.s_
					end

					insPos := 1
					if pad.item (1) = '-' then
						insPos := insPos + 1
					end

					numToPad := (myWholeLength - otherWholeLength).abs
					from
						i := 1
					until
						i > numToPad
					loop
						pad.insert_character ('0', insPos)

						i := i + 1
					end
				end
			end

invariant
	divisionDecimalPrecision_ > 0
end
