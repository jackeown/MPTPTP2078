%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
    ( ~ ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2) )
    | k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:30:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (1609)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.42  % (1609)# SZS output start Saturation.
% 0.22/0.42  tff(u16,negated_conjecture,
% 0.22/0.42      ((~(k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2))) | (k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2)))).
% 0.22/0.42  
% 0.22/0.42  % (1609)# SZS output end Saturation.
% 0.22/0.42  % (1609)------------------------------
% 0.22/0.42  % (1609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (1609)Termination reason: Satisfiable
% 0.22/0.42  
% 0.22/0.42  % (1609)Memory used [KB]: 6012
% 0.22/0.42  % (1609)Time elapsed: 0.003 s
% 0.22/0.42  % (1609)------------------------------
% 0.22/0.42  % (1609)------------------------------
% 0.22/0.42  % (1597)Success in time 0.06 s
%------------------------------------------------------------------------------
