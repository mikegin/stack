note
	description: "Summary description for {MY_STACK}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	MY_STACK[G -> attached ANY]
inherit
	ADT_STACK[G]



create
	make_empty

feature {ADT_STACK} -- Initialization
	imp: LINKED_LIST[G]
		-- implementation

	make_empty
			-- Initialization for `Current'.
		do
			create imp.make
			imp.compare_objects
		end
feature -- model

	model: SEQ[G]
			-- abstract mathematical description of stack
			-- abstraction function
		do
			create Result.make_empty
			across imp as cr loop
				Result.append (cr.item)
			end
		end

feature -- queries
	count: INTEGER
		do
			Result := imp.count
		end

	is_empty: BOOLEAN
	 		-- is the queue empty?
	 	do
	 		Result := imp.is_empty
	 	end


	item: G
			-- Top element of stack ("peek")
		do
			Result := imp.last
		end

	is_equal(other: like Current): BOOLEAN
		do
			Result := imp ~ other.imp
		end

feature -- command
	put(x: G)
			-- push 'x' on top of stack ("push")
		do
			imp.extend(x)
		end


	remove
			-- pop off top of stack ("pop")
		do
			imp.go_i_th (imp.count)
			imp.remove
		end

end
