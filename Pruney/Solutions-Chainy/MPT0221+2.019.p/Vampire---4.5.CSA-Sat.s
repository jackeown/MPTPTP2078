%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u39,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) )).

cnf(u38,negated_conjecture,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) )).

cnf(u34,negated_conjecture,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) )).

cnf(u28,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) )).

cnf(u27,axiom,
    ( r2_hidden(sK3(X0,X1),X1)
    | r1_xboole_0(X0,X1) )).

cnf(u26,axiom,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u24,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u36,negated_conjecture,
    ( ~ r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) )).

cnf(u37,negated_conjecture,
    ( v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) )).

cnf(u23,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X2,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (12324)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.44  % (12340)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % (12324)# SZS output start Saturation.
% 0.21/0.44  cnf(u39,negated_conjecture,
% 0.21/0.44      r1_xboole_0(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.21/0.44  
% 0.21/0.44  cnf(u38,negated_conjecture,
% 0.21/0.44      r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0)).
% 0.21/0.44  
% 0.21/0.44  cnf(u34,negated_conjecture,
% 0.21/0.44      r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.21/0.44  
% 0.21/0.44  cnf(u28,axiom,
% 0.21/0.44      ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)).
% 0.21/0.44  
% 0.21/0.44  cnf(u27,axiom,
% 0.21/0.44      r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)).
% 0.21/0.44  
% 0.21/0.44  cnf(u26,axiom,
% 0.21/0.44      r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 0.21/0.44  
% 0.21/0.44  cnf(u24,axiom,
% 0.21/0.44      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.21/0.44  
% 0.21/0.44  cnf(u36,negated_conjecture,
% 0.21/0.44      ~r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.21/0.44  
% 0.21/0.44  cnf(u37,negated_conjecture,
% 0.21/0.44      v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.21/0.44  
% 0.21/0.44  cnf(u23,axiom,
% 0.21/0.44      ~v1_xboole_0(X0) | ~r2_hidden(X2,X0)).
% 0.21/0.44  
% 0.21/0.44  % (12324)# SZS output end Saturation.
% 0.21/0.44  % (12324)------------------------------
% 0.21/0.44  % (12324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (12324)Termination reason: Satisfiable
% 0.21/0.44  
% 0.21/0.44  % (12324)Memory used [KB]: 1535
% 0.21/0.44  % (12324)Time elapsed: 0.036 s
% 0.21/0.44  % (12324)------------------------------
% 0.21/0.44  % (12324)------------------------------
% 0.21/0.44  % (12322)Success in time 0.083 s
%------------------------------------------------------------------------------
