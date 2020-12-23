%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:35 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,axiom,
    ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X0,X1) )).

cnf(u17,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u28,negated_conjecture,
    ( r1_tarski(sK0,k1_xboole_0) )).

cnf(u14,negated_conjecture,
    ( r1_tarski(sK0,sK2) )).

cnf(u13,negated_conjecture,
    ( r1_tarski(sK0,sK1) )).

cnf(u24,negated_conjecture,
    ( ~ r1_tarski(X0,k4_xboole_0(sK1,sK2))
    | r1_tarski(X0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ r1_tarski(X0,sK1) )).

cnf(u25,negated_conjecture,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(X0,sK1) )).

cnf(u15,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u21,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) )).

cnf(u16,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:35:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18356)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (18364)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (18372)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18356)# SZS output start Saturation.
% 0.21/0.52  cnf(u22,axiom,
% 0.21/0.52      r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u17,axiom,
% 0.21/0.52      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u28,negated_conjecture,
% 0.21/0.52      r1_tarski(sK0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u14,negated_conjecture,
% 0.21/0.52      r1_tarski(sK0,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u13,negated_conjecture,
% 0.21/0.52      r1_tarski(sK0,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u24,negated_conjecture,
% 0.21/0.52      ~r1_tarski(X0,k4_xboole_0(sK1,sK2)) | r1_tarski(X0,k4_xboole_0(sK1,k1_xboole_0)) | ~r1_tarski(X0,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u25,negated_conjecture,
% 0.21/0.52      ~r1_tarski(X0,sK2) | r1_tarski(X0,k1_xboole_0) | ~r1_tarski(X0,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u15,negated_conjecture,
% 0.21/0.52      r1_xboole_0(sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u21,axiom,
% 0.21/0.52      ~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u23,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u16,negated_conjecture,
% 0.21/0.52      k1_xboole_0 != sK0).
% 0.21/0.52  
% 0.21/0.52  % (18356)# SZS output end Saturation.
% 0.21/0.52  % (18356)------------------------------
% 0.21/0.52  % (18356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18356)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (18356)Memory used [KB]: 6140
% 0.21/0.52  % (18356)Time elapsed: 0.103 s
% 0.21/0.52  % (18356)------------------------------
% 0.21/0.52  % (18356)------------------------------
% 0.21/0.53  % (18349)Success in time 0.162 s
%------------------------------------------------------------------------------
