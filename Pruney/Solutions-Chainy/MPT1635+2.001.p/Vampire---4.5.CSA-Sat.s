%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 1.27s
% Output     : Saturation 1.27s
% Verified   : 
% Statistics : Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK1) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2) )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u17,axiom,
    ( ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u19,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u21,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u16,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u26,axiom,
    ( ~ r1_tarski(X0,X2)
    | r2_hidden(sK2(X0,X1),X2)
    | r1_tarski(X0,X1) )).

cnf(u13,negated_conjecture,
    ( k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (794099712)
% 0.13/0.39  ipcrm: permission denied for id (794132502)
% 0.21/0.49  ipcrm: permission denied for id (794165346)
% 1.27/0.72  % (24197)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.72  % SZS status CounterSatisfiable for theBenchmark
% 1.27/0.72  % (24197)# SZS output start Saturation.
% 1.27/0.72  cnf(u27,negated_conjecture,
% 1.27/0.72      m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u12,negated_conjecture,
% 1.27/0.72      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.27/0.72  
% 1.27/0.72  cnf(u20,axiom,
% 1.27/0.72      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)).
% 1.27/0.72  
% 1.27/0.72  cnf(u18,axiom,
% 1.27/0.72      r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u17,axiom,
% 1.27/0.72      ~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u19,axiom,
% 1.27/0.72      ~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u21,axiom,
% 1.27/0.72      r1_tarski(X1,X1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u16,axiom,
% 1.27/0.72      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 1.27/0.72  
% 1.27/0.72  cnf(u26,axiom,
% 1.27/0.72      ~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)).
% 1.27/0.72  
% 1.27/0.72  cnf(u13,negated_conjecture,
% 1.27/0.72      k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1)).
% 1.27/0.72  
% 1.27/0.72  % (24197)# SZS output end Saturation.
% 1.27/0.72  % (24197)------------------------------
% 1.27/0.72  % (24197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.72  % (24197)Termination reason: Satisfiable
% 1.27/0.72  
% 1.27/0.72  % (24197)Memory used [KB]: 6140
% 1.27/0.72  % (24197)Time elapsed: 0.111 s
% 1.27/0.72  % (24197)------------------------------
% 1.27/0.72  % (24197)------------------------------
% 1.27/0.73  % (24213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.66/0.73  % (24216)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.73  % (24021)Success in time 0.373 s
%------------------------------------------------------------------------------
