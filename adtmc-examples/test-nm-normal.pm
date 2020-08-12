//concrete example w/ 2 clients and 2 servers.

dtmc

formula c1_connected_server_has_sth = (c1s=1 & s1_sth=1) | (c1s=2 & s2_sth=1);
formula c2_connected_server_has_sth = (c2s=1 & s1_sth=1) | (c2s=2 & s2_sth=1);
formula updated_client_gossips = (c1_sth=1 & c1_skip=false) | (c2_sth=1 & c2_skip=false);
formula nonupdated_client_gossips = (c1_sth=0 & c1_skip=false) | (c2_sth=0 & c2_skip=false);
formula s1_connected_client_has_sth = (c1s=1 & c1_sth=1) | (c2s=1 & c2_sth=1);
formula s2_connected_client_has_sth = (c1s=2 & c1_sth=1) | (c2s=2 & c2_sth=1);

// FORMULAE FOR ABSTRACT VARIABLES
formula abs_c_sth = 0 + (c1!=2?c1_sth+c2_sth:0) +
		(c1=2 & ( (c1_sth=0 & c1_connected_server_has_sth) | c1_sth=1 )?1:0) +
		(c1=2 & ( (c2_sth=0 & c2_connected_server_has_sth) | c2_sth=1 )?1:0);

formula abs_stage = 0 + (c1=1 & (updated_client_gossips & !nonupdated_client_gossips)?1:0) +
				(c1=1 & (!updated_client_gossips & nonupdated_client_gossips)?2:0) + 
				(c1=1 & (updated_client_gossips & nonupdated_client_gossips)?3:0) + 
				(c1=1 & !(updated_client_gossips | nonupdated_client_gossips)?4:0) +
				(c1=2?5:0) +
				(c1=3?6:0) + 
    			(c1=4?7:0);

formula abs_s_sth = 0 + (c1!=2?s1_sth+s2_sth:0) +
		  			(c1=2 & ( (s1_sth=0 & s1_connected_client_has_sth) | s1_sth=1 )?1:0) +
		 			(c1=2 & ( (s2_sth=0 & s2_connected_client_has_sth) | s2_sth=1 )?1:0);

label "abs_t" = abs_c_sth=2;

// NB: An error must be raised with state abstraction fails e.g.
// unable to find value for an abstract variable given a state. 

//initial states for each client
const int c1_sth_init = 1;
const int c2_sth_init = 0;

//client connect rates
prob g1 = 0.2;
prob g2 = 0.8;

//client profiles
prob p_1_1 = 3/5;
prob p_1_2 = 2/5;

prob p_2_1 = 1/4;
prob p_2_2 = 3/4;

module Client1 

	c1 : [0..4] init 0;
	c1s : [0..2] init 0;
	c1_sth : [0..1] init c1_sth_init;
	c1_skip : bool init false;

	[connect] c1=0 -> g1 : (c1'=1) + 1-g1 : (c1'=1)&(c1_skip'=true);
	[choose] c1_skip=false & c1=1 -> p_1_1 : (c1'=2)&(c1s'=1) + p_1_2 : (c1'=2)&(c1s'=2);
	[choose] c1_skip=true & c1=1 -> (c1'=2);
	[update] c1=2 & c1_skip=false & connected_server_has_sth  -> (c1'=3) & (c1_sth'=1) & (c1s'=0) & (c1_skip'=false);
	[update] c1=2 & ((c1_skip=false & !connected_server_has_sth) | c1_skip=true) -> (c1'=3) & (c1s'=0) & (c1_skip'=false);
	[round_complete] c1=3 & !clients_all_updated -> (c1'=0);
	[round_complete] c1=3 & clients_all_updated -> (c1'=4);
	[END] c1=4 -> true;

endmodule

formula connected_server_has_sth = ((c1s=1 & s1_sth=1) | (c1s=2 & s2_sth=1));
formula clients_all_updated = c1_sth=1&c2_sth=1;

//must check that for every concrete state for which the label is 
label "all_fresh" = c1_sth=1&c2_sth=1;

module Client2=Client1[p_1_1=p_2_1,p_1_2=p_2_2,
g1=g2, c1=c2, c1s=c2s, c1_sth=c2_sth, c2_sth=c1_sth, c1_skip=c2_skip, c1_sth_init = c2_sth_init] endmodule

const int S1 = 1;
const int S2 = 2;

const int s1_init = 1;
const int s2_init = 0;

module Server1

	s1_sth : [0..1] init s1_init;

	[update] s1_sth=0 & connected_client_has_sth -> (s1_sth'=1);
	[update] s1_sth=1 | (s1_sth=0 & !connected_client_has_sth) -> true;
	[round_complete] clients_all_updated -> (s1_sth'=0);
	[round_complete] !clients_all_updated -> true;
	[END] true -> true;

endmodule

formula connected_client_has_sth = (c1s=S1 & c1_sth=1) | (c2s=S1 & c2_sth=1);

module Server2=Server1[s1_sth=s2_sth, s2_sth=s1_sth, S1=S2, s1_init=s2_init] endmodule
