%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
cnf(u24,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u15,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (22537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (22536)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (22536)# SZS output start Saturation.
% 0.21/0.52  cnf(u24,axiom,
% 0.21/0.52      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u15,axiom,
% 0.21/0.52      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (22536)# SZS output end Saturation.
% 0.21/0.52  % (22536)------------------------------
% 0.21/0.52  % (22536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22536)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (22536)Memory used [KB]: 6140
% 0.21/0.52  % (22536)Time elapsed: 0.091 s
% 0.21/0.52  % (22536)------------------------------
% 0.21/0.52  % (22536)------------------------------
% 0.21/0.52  % (22530)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (22529)Success in time 0.147 s
%------------------------------------------------------------------------------
