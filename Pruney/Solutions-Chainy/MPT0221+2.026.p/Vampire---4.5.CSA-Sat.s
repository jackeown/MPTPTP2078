%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:48 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u14,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (5803)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (5795)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.49  % (5787)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.49  % (5803)Refutation not found, incomplete strategy% (5803)------------------------------
% 0.19/0.49  % (5803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (5803)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (5803)Memory used [KB]: 10618
% 0.19/0.49  % (5803)Time elapsed: 0.043 s
% 0.19/0.49  % (5803)------------------------------
% 0.19/0.49  % (5803)------------------------------
% 0.19/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.49  % (5787)# SZS output start Saturation.
% 0.19/0.49  cnf(u21,axiom,
% 0.19/0.49      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u14,axiom,
% 0.19/0.49      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.19/0.49  
% 0.19/0.49  cnf(u23,negated_conjecture,
% 0.19/0.49      k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)).
% 0.19/0.49  
% 0.19/0.49  % (5787)# SZS output end Saturation.
% 0.19/0.49  % (5787)------------------------------
% 0.19/0.49  % (5787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (5787)Termination reason: Satisfiable
% 0.19/0.49  
% 0.19/0.49  % (5787)Memory used [KB]: 6140
% 0.19/0.49  % (5787)Time elapsed: 0.057 s
% 0.19/0.49  % (5787)------------------------------
% 0.19/0.49  % (5787)------------------------------
% 0.19/0.50  % (5780)Success in time 0.142 s
%------------------------------------------------------------------------------
