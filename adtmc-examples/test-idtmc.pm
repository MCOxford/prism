// at the moment, only want to abstract dtmcs but may want to look into abstracting ctmcs in the future
dtmc

// FORMULAE FOR ABSTRACT VARIABLES
formula abs_a = 0 + (s=1|s=2?1:0) + (s=3|s=5?2:0) + (s=4?3:0);
label "abs_t" = abs_a=3;

module concrete

	s : [0..5] init 0;

	[] s=0 -> [1, 1] : (s'=1);
	[] s=1 -> [0.3, 0.4] : (s'=2) + [0.1, 0.6] : (s'=3) + [0.2, 0.7] : (s'=4);
	[] s=2 -> [0.4, 0.5] : (s'=1) + [0.3, 0.7] : (s'=4);
	[] s=3 -> [0.1, 1] : (s'=2) + [0.2, 0.3] : (s'=5);
	[] s=4 -> [1, 1] : true;
	[] s=5 -> [0.1, 0.6] : (s'=1) + [0.2, 0.5] : (s'=2);

endmodule
