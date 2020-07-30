// at the moment, only want to abstract dtmcs but may want to look into abstracting ctmcs in the future
dtmc

// FORMULAE FOR ABSTRACT VARIABLES
formula abs_a = (s=1||s=2?1:0) + (s=5||s=6?2:0) + (s=3||s=4?3:0);

module concrete

	s : [0..6] init 0

	[] s=0 -> 1/3 : (s'=1) + 2/3 : (s'=3);
	[] s=1 -> 1/2 : (s'=2) + 1/2 : (s'=3);
	[] s=2 -> 1 : (s'=6);
	[] s=3 -> 1 : (s'=4);
	[] s=4 -> 3/5 : (s'=2) + 2/5 : (s'=3);
	[] s=5 -> 1 : (s'=6);
	[] s=6 -> 1/2 : true + 1/2 : (s'=5);

end module

// desired result
//
// .sta file:
//
// (a)
// 0:(0)
// 1:(1)
// 2:(2)
// 3:(3)
//
// .tra file:
//
// 4 8
// 0 1 [1/3, 1/3]
// 0 3 [2/3, 2/3]
// 1 1 [0, 1/2] <- will need to swap 0 for 10E-14 in this instance so as not to affect qualitative properties
// 1 2 [0, 1]
// 1 3 [0, 1/2]
// 2 2 [1 ,1]
// 3 1 [0, 3/5]
// 3 3 [2/5, 1]
//
// .lab file:
// 0 = "init"
// 0: 0

// once the abstract model is constructed, analyse for properties such as:
// Pmin=? [ F a=2 ]
// Pmax=? [ F a=2 ]

// in three-valued abstraction, a proposition may be true (true in every state represented by the abstract state), 
// false (false in every state represented by the abstract state) or undecided (otherwise). For now, will only deal
// with labels that are either true or false.

// assume that model are single initial states
