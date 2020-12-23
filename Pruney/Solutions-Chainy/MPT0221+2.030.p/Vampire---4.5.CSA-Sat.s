%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u16,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u19,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) )).

cnf(u28,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u26,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) )).

cnf(u27,axiom,
    ( k1_xboole_0 = sK3 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (4945)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (4937)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (4929)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 0.21/0.50  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4945)Memory used [KB]: 10618
% 0.21/0.50  % (4945)Time elapsed: 0.051 s
% 0.21/0.50  % (4945)------------------------------
% 0.21/0.50  % (4945)------------------------------
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (4929)# SZS output start Saturation.
% 0.21/0.50  cnf(u24,axiom,
% 0.21/0.50      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u16,axiom,
% 0.21/0.50      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u18,axiom,
% 0.21/0.50      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u19,axiom,
% 0.21/0.50      ~r2_hidden(X0,X1) | ~v1_xboole_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u28,axiom,
% 0.21/0.50      v1_xboole_0(k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u26,axiom,
% 0.21/0.50      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u30,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,axiom,
% 0.21/0.50      k1_xboole_0 = sK3).
% 0.21/0.50  
% 0.21/0.50  % (4929)# SZS output end Saturation.
% 0.21/0.50  % (4929)------------------------------
% 0.21/0.50  % (4929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4929)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (4929)Memory used [KB]: 6140
% 0.21/0.50  % (4929)Time elapsed: 0.065 s
% 0.21/0.50  % (4929)------------------------------
% 0.21/0.50  % (4929)------------------------------
% 0.21/0.50  % (4922)Success in time 0.145 s
%------------------------------------------------------------------------------
