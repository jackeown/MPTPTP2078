%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u10,negated_conjecture,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) )).

cnf(u7,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) )).

cnf(u8,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 )).

cnf(u9,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) )).

cnf(u17,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u12,axiom,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) )).

cnf(u15,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u18,axiom,
    ( r2_xboole_0(X0,k2_xboole_0(X0,X1))
    | k2_xboole_0(X0,X1) = X0 )).

cnf(u13,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u16,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

cnf(u11,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (9267)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.45  % (9267)Refutation not found, incomplete strategy% (9267)------------------------------
% 0.20/0.45  % (9267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (9267)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (9267)Memory used [KB]: 10618
% 0.20/0.45  % (9267)Time elapsed: 0.007 s
% 0.20/0.45  % (9267)------------------------------
% 0.20/0.45  % (9267)------------------------------
% 0.20/0.50  % (9261)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (9261)Refutation not found, incomplete strategy% (9261)------------------------------
% 0.20/0.50  % (9261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9261)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9261)Memory used [KB]: 6012
% 0.20/0.50  % (9261)Time elapsed: 0.082 s
% 0.20/0.50  % (9261)------------------------------
% 0.20/0.50  % (9261)------------------------------
% 0.20/0.51  % (9268)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (9257)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (9256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (9268)# SZS output start Saturation.
% 0.20/0.51  cnf(u10,negated_conjecture,
% 0.20/0.51      r3_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u7,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK0,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u8,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | sK0 != sK1).
% 0.20/0.51  
% 0.20/0.51  cnf(u9,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u17,axiom,
% 0.20/0.51      r1_tarski(X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u12,axiom,
% 0.20/0.51      r1_tarski(X0,k2_xboole_0(X0,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u15,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u18,axiom,
% 0.20/0.51      r2_xboole_0(X0,k2_xboole_0(X0,X1)) | k2_xboole_0(X0,X1) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u13,axiom,
% 0.20/0.51      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u16,axiom,
% 0.20/0.51      ~r2_xboole_0(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u11,axiom,
% 0.20/0.51      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.51  
% 0.20/0.51  % (9268)# SZS output end Saturation.
% 0.20/0.51  % (9268)------------------------------
% 0.20/0.51  % (9268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9268)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (9268)Memory used [KB]: 1535
% 0.20/0.51  % (9268)Time elapsed: 0.077 s
% 0.20/0.51  % (9268)------------------------------
% 0.20/0.51  % (9268)------------------------------
% 0.20/0.51  % (9244)Success in time 0.163 s
%------------------------------------------------------------------------------
