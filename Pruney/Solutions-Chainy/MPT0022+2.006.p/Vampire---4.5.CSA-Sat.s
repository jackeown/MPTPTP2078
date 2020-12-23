%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u9,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u10,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u7,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1) )).

cnf(u8,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:12:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (27794)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (27797)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (27794)Refutation not found, incomplete strategy% (27794)------------------------------
% 0.22/0.47  % (27794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (27794)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (27794)Memory used [KB]: 10490
% 0.22/0.47  % (27794)Time elapsed: 0.049 s
% 0.22/0.47  % (27794)------------------------------
% 0.22/0.47  % (27794)------------------------------
% 0.22/0.47  % (27797)Refutation not found, incomplete strategy% (27797)------------------------------
% 0.22/0.47  % (27797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (27797)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  % (27807)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (27811)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (27807)Refutation not found, incomplete strategy% (27807)------------------------------
% 0.22/0.48  % (27807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27807)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27807)Memory used [KB]: 1535
% 0.22/0.48  % (27807)Time elapsed: 0.061 s
% 0.22/0.48  % (27807)------------------------------
% 0.22/0.48  % (27807)------------------------------
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (27811)# SZS output start Saturation.
% 0.22/0.48  cnf(u9,axiom,
% 0.22/0.48      v1_xboole_0(k1_xboole_0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u10,axiom,
% 0.22/0.48      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.22/0.48  
% 0.22/0.48  cnf(u7,negated_conjecture,
% 0.22/0.48      k1_xboole_0 = k2_xboole_0(sK0,sK1)).
% 0.22/0.48  
% 0.22/0.48  cnf(u8,negated_conjecture,
% 0.22/0.48      k1_xboole_0 != sK0).
% 0.22/0.48  
% 0.22/0.48  % (27811)# SZS output end Saturation.
% 0.22/0.48  % (27811)------------------------------
% 0.22/0.48  % (27811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27811)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (27811)Memory used [KB]: 1535
% 0.22/0.48  % (27811)Time elapsed: 0.060 s
% 0.22/0.48  % (27811)------------------------------
% 0.22/0.48  % (27811)------------------------------
% 0.22/0.48  
% 0.22/0.48  % (27789)Success in time 0.119 s
%------------------------------------------------------------------------------
