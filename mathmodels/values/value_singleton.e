note
	description: "Summary description for {VALUE2_SINGLETON}."
	author: ""
	date: "$Date: 2010-12-13 16:07:07 -0500 (Mon, 13 Dec 2010) $"
	revision: "$Revision$"

class
	VALUE_SINGLETON
inherit ANY
	redefine default_create end
create
	default_create
feature{NONE}
	default_create
		do
			epsilon := "0.0"
		end
feature
	epsilon: VALUE

	set_epsilon (v: STRING)
		do
			epsilon := v
		ensure

		end

end
