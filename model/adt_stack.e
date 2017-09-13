note
	description: "[
		Abstract Data Type for a Stack, with value semantics.
		Classic contracts vs. Complete contracts with a model.
		]"
	author: "JSO"
	date: "$Date$"
	revision: "$Revision$"

deferred class
	ADT_STACK[G -> attached ANY]
inherit
	ANY
		undefine is_equal end

feature -- model
	model: SEQ[G]
			-- abstract mathematical description of stack
			-- abstraction function
		deferred
		end

feature -- queries
	count: INTEGER
		-- number of items in stack
		deferred
		ensure
		 complete: Result = model.count
		end

	is_empty: BOOLEAN
	 		-- is the queue empty?
	 	deferred
	 	ensure
	 		complete: Result = model.is_empty
	 	end

	item: G
			-- Top element of stack ("peek")
		require
			not is_empty
		deferred
		ensure
			complete: Result ~ model.last
		end

	is_equal(other: like Current): BOOLEAN
		deferred
		ensure then
			complete: model ~ other.model
		end

feature -- commands
	make_empty
			-- Initialization for `Current'.
		deferred
		ensure
			classic: is_empty
		end

	put(x: G)
			-- push 'x' on top of stack ("push")
		deferred
		ensure
			classic: count = old count + 1
			classic: item ~ x
			complete: model ~ ((old model) |-> x)
		end

	remove
			-- pop off top of stack ("pop")
		require
			not is_empty
		deferred
		ensure
			classic: count = old count - 1
			complete: (old model) ~ (model |-> (old item))
		end

feature -- axioms
	axiom (x: G)
		do
			Current.put(x)
			Current.remove
		ensure
			model ~ (old model)
		end
end
