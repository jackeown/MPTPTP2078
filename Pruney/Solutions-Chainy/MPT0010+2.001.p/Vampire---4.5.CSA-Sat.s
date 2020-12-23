%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:31 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u11,negated_conjecture,
    ( r1_tarski(sK0,k1_xboole_0) )).

cnf(u14,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u15,axiom,
    ( ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X0,X1)
    | r2_hidden(X2,X1) )).

cnf(u13,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u12,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (11166)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (11182)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (11166)# SZS output start Saturation.
% 0.22/0.50  cnf(u11,negated_conjecture,
% 0.22/0.50      r1_tarski(sK0,k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u14,axiom,
% 0.22/0.50      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u15,axiom,
% 0.22/0.50      ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u13,axiom,
% 0.22/0.50      v1_xboole_0(k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u12,negated_conjecture,
% 0.22/0.50      k1_xboole_0 != sK0).
% 0.22/0.50  
% 0.22/0.50  % (11166)# SZS output end Saturation.
% 0.22/0.50  % (11166)------------------------------
% 0.22/0.50  % (11166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11166)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (11166)Memory used [KB]: 6140
% 0.22/0.50  % (11166)Time elapsed: 0.088 s
% 0.22/0.50  % (11166)------------------------------
% 0.22/0.50  % (11166)------------------------------
% 0.22/0.50  % (11159)Success in time 0.14 s
%------------------------------------------------------------------------------
