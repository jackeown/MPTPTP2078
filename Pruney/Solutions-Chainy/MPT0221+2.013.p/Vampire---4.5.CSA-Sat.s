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
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u66,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u73,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | r1_xboole_0(X2,X3) )).

cnf(u48,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | v1_xboole_0(X0) )).

cnf(u44,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(k3_xboole_0(X0,X1)) )).

cnf(u35,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u82,axiom,
    ( ~ r1_xboole_0(X2,X3)
    | r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) )).

cnf(u76,axiom,
    ( r2_hidden(sK3(X1,X1),X1)
    | r1_xboole_0(X1,X1) )).

cnf(u33,axiom,
    ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u30,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u45,axiom,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0) )).

cnf(u34,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u29,axiom,
    ( ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u46,axiom,
    ( ~ r2_hidden(X3,X2)
    | ~ r1_xboole_0(X2,X2) )).

cnf(u57,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u78,axiom,
    ( ~ v1_xboole_0(X1)
    | r1_xboole_0(X1,X1) )).

cnf(u74,axiom,
    ( ~ v1_xboole_0(k3_xboole_0(X4,X5))
    | r1_xboole_0(X4,X5) )).

cnf(u31,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u53,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

cnf(u27,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u65,axiom,
    ( k1_xboole_0 != X1
    | r1_xboole_0(X1,X1) )).

cnf(u36,axiom,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (855)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (855)# SZS output start Saturation.
% 0.21/0.43  cnf(u66,axiom,
% 0.21/0.43      r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u73,axiom,
% 0.21/0.43      ~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) | r1_xboole_0(X2,X3)).
% 0.21/0.43  
% 0.21/0.43  cnf(u48,axiom,
% 0.21/0.43      ~r1_xboole_0(X0,X0) | v1_xboole_0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u44,axiom,
% 0.21/0.43      ~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))).
% 0.21/0.43  
% 0.21/0.43  cnf(u35,axiom,
% 0.21/0.43      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.43  
% 0.21/0.43  cnf(u82,axiom,
% 0.21/0.43      ~r1_xboole_0(X2,X3) | r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))).
% 0.21/0.43  
% 0.21/0.43  cnf(u76,axiom,
% 0.21/0.43      r2_hidden(sK3(X1,X1),X1) | r1_xboole_0(X1,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u33,axiom,
% 0.21/0.43      r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u30,axiom,
% 0.21/0.43      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u45,axiom,
% 0.21/0.43      ~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u34,axiom,
% 0.21/0.43      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u29,axiom,
% 0.21/0.43      ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u46,axiom,
% 0.21/0.43      ~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)).
% 0.21/0.43  
% 0.21/0.43  cnf(u57,negated_conjecture,
% 0.21/0.43      v1_xboole_0(k1_xboole_0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u78,axiom,
% 0.21/0.43      ~v1_xboole_0(X1) | r1_xboole_0(X1,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u74,axiom,
% 0.21/0.43      ~v1_xboole_0(k3_xboole_0(X4,X5)) | r1_xboole_0(X4,X5)).
% 0.21/0.43  
% 0.21/0.43  cnf(u31,axiom,
% 0.21/0.43      k3_xboole_0(X0,X0) = X0).
% 0.21/0.43  
% 0.21/0.43  cnf(u53,negated_conjecture,
% 0.21/0.43      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u27,axiom,
% 0.21/0.43      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u65,axiom,
% 0.21/0.43      k1_xboole_0 != X1 | r1_xboole_0(X1,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u36,axiom,
% 0.21/0.43      k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)).
% 0.21/0.43  
% 0.21/0.43  % (855)# SZS output end Saturation.
% 0.21/0.43  % (855)------------------------------
% 0.21/0.43  % (855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (855)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (855)Memory used [KB]: 1663
% 0.21/0.43  % (855)Time elapsed: 0.004 s
% 0.21/0.43  % (855)------------------------------
% 0.21/0.43  % (855)------------------------------
% 0.21/0.43  % (840)Success in time 0.073 s
%------------------------------------------------------------------------------
