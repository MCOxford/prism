dtmc

formula c1_detection = c1d || (c1s=1 & s1_sth+c1_sth=3) || (c1s=2 & s2_sth+c1_sth=3);
formula c2_detection = c2d || (c2s=1 & s1_sth+c2_sth=3) || (c2s=2 & s2_sth+c2_sth=3);
formula updated_client_gossips = (c1_sth>0 & c1_skip=false) || (c2_sth>0 & c2_skip=false);
formula nonupdated_client_gossips = (c1_sth=0 & c1_skip=false) || (c2_sth=0 & c2_skip=false);

// FORMULAE FOR ABSTRACT VARIABLES
formula abs_cd = (c1!=2 & (c1d||c2d)) ||
			 	 (c1=2 & c1_detection) ||
			 	 (c1=2 & c2_detection);

formula abs_stage = 0 + (c1=1 & updated_client_gossips?2:0) +
					(c1=1 & nonupdated_client_gossips?2:0) + 
					(c1=1 & !(updated_client_gossips || nonupdated_client_gossips)?4:0) +
					(c1=2?5:0) +
					(c1=3?6:0) +
    				(c1=4?7:0);

formula abs_sd = s1d || s2d;

const int c1_sth_init = 0;
const int c2_sth_init = 2;

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
	c1_sth : [0..2] init c1_sth_init;
	c1d : bool init false;
	c1_skip : bool init false;

	[connect] c1=0 -> g1 : (c1'=1) + 1-g1 : (c1'=1) & (c1_skip'=true);
	[choose] !c1_skip & c1=1 -> p_1_1 : (c1'=2)&(c1s'=1) + p_1_2 : (c1'=2)&(c1s'=2);
	[choose] c1_skip & c1=1 -> (c1'=2);.
	[update] !c1_skip & c1=2 & s_data_ok -> (c1_sth'=c_update) & (c1'=3);
	[update] !c1_skip & c1=2 & !s_data_ok -> (c1d'=true) & (c1'=3);
 	[update] c1_skip & c1=2 -> (c1'=3);
	[round_complete] c1=3 & !detect -> (c1'=0) & (c1s'=0) & (c1_skip'=false);
	[round_complete] c1=3 & detect -> (c1'=4) & (c1s'=0) & (c1_skip'=false);
	[END] c1=4 -> true;

endmodule

formula pr_req_successful = (c1s=1 & s1_sth+c1_sth!=3) | (c1s=2 & s2_sth+c1_sth!=3);

formula warn_msg = (c1s=1 & s1d) | (c1s=2 & s2d);

formula c_update = c1_sth + ((c1s=1 & s1_sth>c1_sth)?s1_sth-c1_sth:0) + ((c1s=2 & s2_sth>c1_sth)?s2_sth-c1_sth:0);

formula s_data_ok = pr_req_successful & !warn_msg;

formula detect = c1d | c2d;
label "detect" = c1d | c2d;

module Client2=Client1[p_1_1=p_2_1, p_1_2=p_2_2,
g1=g2,
c1=c2, c1s=c2s, c1_sth=c2_sth, c1_skip=c2_skip, c1d=c2d, c2d=c1d,
c1_sth_init = c2_sth_init] endmodule

const int S1 = 1;
const int S2 = 2;

const int s1_init = 1;
const int s2_init = 0;

module Server1

	s1_sth : [0..2] init s1_init;
	s1d : bool init false;

	[update] !s1d & c_data_ok -> (s1_sth'=s_update);
	[update] !s1d & !c_data_ok -> (s1d'=true) & (s1_sth'=0);
	[update] s1d -> true;
	[END] true -> true;

endmodule

formula server_pr_req_fail = (c1s=S1 & s1_sth+c1_sth=3) | (c2s=S1 & s1_sth+c2_sth=3);
formula pairwise_inconsistency = ((c1s=S1 & c1_sth=1) | (c2s=S1 & c2_sth=1)) & 
				 				 ((c1s=S1 & c1_sth=2) | (c2s=S1 & c2_sth=2));
formula c_data_ok = !server_pr_req_fail & !pairwise_inconsistency;

formula s_update = s1_sth + max((c1s=S1&c1_sth>s1_sth?c1_sth-s1_sth:0), (c2s=S1&c2_sth>s1_sth?c2_sth-s1_sth:0));

module Server2=Server1[s1_sth=s2_sth, s2_sth=s1_sth, s1d=s2d, s2d=s1d, S1=S2, s1_init=s2_init] endmodule
