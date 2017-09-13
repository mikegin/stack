note
	description: "Summary description for {TESTS}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	TESTS
inherit
	ES_TEST

create
	make

feature {NONE} -- Initialization

	make
			-- Initialization for `Current'.
		do
			add_boolean_case (agent t0)
			add_boolean_case (agent t1)
			add_boolean_case (agent t2)
			add_boolean_case (agent t3)
			add_boolean_case (agent t4)

		end

feature -- tests
	t0: BOOLEAN
		local
			s1, s2, s1_old: SEQ[INTEGER]
			a1, a2: ARRAY[INTEGER]
		do
			comment("t0: basic tests SEQ[INTEGER] expanded uses =")
			a1 := <<8, 4, 6, 2>>
			a2 := <<4, 6, 2>>
			create s1.make_from_array (a1)
			create s2.make_from_array (a2)
			create s1_old.make_from_array (a1)
			assert ("empty", not s1.is_empty, s1)
			Result := s1.count = 4 and s1.first = 8 and s1.last = 2
			check Result end
			assert_equal ("tail", s1.tail, s2)
			Result := s1.tail /= s2 and s1.tail ~ s2
			check Result end
			s2 := s1 |<- 10
			assert_equal("prepended", s2.first = 10 and s2.tail ~ s1, True)
			s2 := s1 |-> 0
			assert_equal("appended", s2.last, 0)
			assert_equal("appended", s2.first, 8)
			assert_equal("s1 unchanged", s1, s1_old)
		end

	t1: BOOLEAN
		local
			s1, s2, s1_old: SEQ[STRING]
			a1, a2: ARRAY[STRING]
		do
			comment("t1: basic tests SEQ[STRING] reference requires ~")
			a1 := <<"8", "4", "6", "2">>
			a2 := <<"4", "6", "2">>
			create s1.make_from_array (a1)
			create s2.make_from_array (a2)
			create s1_old.make_from_array (a1)
			assert ("empty", not s1.is_empty, s1)
			Result := s1.count = 4 and s1.first ~ "8" and s1.last ~ "2"
			check Result end
			assert_equal ("tail", s1.tail, s2)
			Result := s1.tail /= s2 and s1.tail ~ s2
			check Result end
			s2 := s1 |<- "10"
			assert_equal("prepended", s2.first ~ "10" and s2.tail ~ s1, True)
			s2 := s1 |-> "0"
			assert_equal("appended", s2.last, "0")
			assert_equal("appended", s2.first, "8")
			assert_equal("s1 unchanged", s1, s1_old)
		end

	t2: BOOLEAN
		local
			stk: MY_STACK[STRING]
		do
			comment("t2: basic tests MY_STACK[STRING]")
			-- create empty stack and check
			create stk.make_empty
			Result := stk.is_empty
			check Result end
			-- put three items and check
			stk.put ("one")
			stk.put ("two")
			stk.put ("three")
			assert_equal ("item three", stk.item, "three")
			assert_equal ("count 3", stk.count, 3)
			-- remove one item and check
			stk.remove
			assert_equal ("item two", stk.item, "two")
			assert_equal ("count 2", stk.count, 2)
		end

	t3: BOOLEAN
		local
			stk1, stk2: MY_STACK[STRING]
		do
			comment("t3: compare two MY_STACK[STRING]")
			-- create empty stack and check
			create stk1.make_empty
			create stk2.make_empty
			-- put three items and check
			stk1.put ("one")
			stk2.put ("one")
			Result := stk1 ~ stk2
		end

	t4: BOOLEAN
		local
			stk: MY_STACK[STRING]
		do
			comment("t4: MY_STACK[STRING] axiom")
			-- create empty stack and check
			create stk.make_empty
			stk.put ("hello")
			stk.axiom ("goodbye")
			Result := stk.item ~ "hello" and stk.count = 1
		end

feature -- JSO tests

end
