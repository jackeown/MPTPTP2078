%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u16,negated_conjecture,
    ( ~ ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2) )
    | k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.41  % (31970)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.13/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.13/0.41  % (31970)# SZS output start Saturation.
% 0.13/0.41  tff(u16,negated_conjecture,
% 0.13/0.41      ((~(k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2))) | (k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2)))).
% 0.13/0.41  
% 0.13/0.41  % (31970)# SZS output end Saturation.
% 0.13/0.41  % (31970)------------------------------
% 0.13/0.41  % (31970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (31970)Termination reason: Satisfiable
% 0.13/0.41  
% 0.13/0.41  % (31970)Memory used [KB]: 6012
% 0.13/0.41  % (31970)Time elapsed: 0.003 s
% 0.13/0.41  % (31970)------------------------------
% 0.13/0.41  % (31970)------------------------------
% 0.21/0.41  % (31967)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (31959)Success in time 0.056 s
%------------------------------------------------------------------------------
