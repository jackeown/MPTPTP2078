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
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u14,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u13,negated_conjecture,(
    r1_tarski(sK1,sK2) )).

tff(u12,negated_conjecture,(
    r2_yellow_0(sK0,sK1) )).

tff(u11,negated_conjecture,(
    r2_yellow_0(sK0,sK2) )).

tff(u10,negated_conjecture,(
    ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (16991)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  % (16984)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (16984)# SZS output start Saturation.
% 0.20/0.47  tff(u14,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u13,negated_conjecture,
% 0.20/0.47      r1_tarski(sK1,sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u12,negated_conjecture,
% 0.20/0.47      r2_yellow_0(sK0,sK1)).
% 0.20/0.47  
% 0.20/0.47  tff(u11,negated_conjecture,
% 0.20/0.47      r2_yellow_0(sK0,sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u10,negated_conjecture,
% 0.20/0.47      ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))).
% 0.20/0.47  
% 0.20/0.47  % (16984)# SZS output end Saturation.
% 0.20/0.47  % (16984)------------------------------
% 0.20/0.47  % (16984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16984)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (16984)Memory used [KB]: 5245
% 0.20/0.47  % (16984)Time elapsed: 0.050 s
% 0.20/0.47  % (16984)------------------------------
% 0.20/0.47  % (16984)------------------------------
% 0.20/0.47  % (16977)Success in time 0.11 s
%------------------------------------------------------------------------------
