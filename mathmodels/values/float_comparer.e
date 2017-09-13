note
	description: "[
		Compare two reals x and y within epsilon.
		(x |~| y).rounded_to(epsilon): 
			This is an equivalence relation.
			Bin sizes are of length epsilon (the precision) centered at a representive defined
			by the the 'round' function. Representative r for float x is: (x/epsilon+.5).floor. 
			Floats x and y are in the same bin iff they have the same representatives.
			The bins are centered at zero and then distributed symetrically in the positive 
			and negative directions. If x and y are in the same bin and y and z
			are in the same bin, then a and z are also in the same bin.
		(x |~| y).within(epsilon):
			This is not an equivalence relation. It is _not_ the case that
			if x and y are within epsilon and y and z are withn epsilon
			then x and z are within epsilon.
	]"
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	FLOAT_COMPARER



create
	make
feature {NONE}
	first: FLOAT
	second: FLOAT

	make(r1,r2: FLOAT)
		do
			first := r1
			second := r2
		end
feature

	round (x, bin: FLOAT): FLOAT
		do
			Result := (x / bin).rounded_real_64
--			Result := ((x/bin)+0.5).floor
		end

	rounded_to(epsilon: FLOAT): BOOLEAN
			-- equivalence relation based on 'round'
		require
			epsilon >= 0
		do
			Result := round (first, epsilon) = round (second, epsilon)
		end

	within(epsilon: FLOAT): BOOLEAN
			-- not equivalence relation
			-- violates transitivity
		require
			epsilon >= 0
		do
			Result :=  (first-second).abs <= epsilon
		end
end
