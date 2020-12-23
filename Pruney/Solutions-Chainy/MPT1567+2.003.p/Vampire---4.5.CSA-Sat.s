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
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u16,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u15,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u14,negated_conjecture,(
    v2_yellow_0(sK0) )).

tff(u13,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u12,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u11,negated_conjecture,(
    ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3662)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (3660)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.51  % (3668)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.51  % (3670)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (3660)# SZS output start Saturation.
% 0.21/0.51  tff(u16,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  tff(u15,negated_conjecture,
% 0.21/0.51      v5_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  tff(u14,negated_conjecture,
% 0.21/0.51      v2_yellow_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  tff(u13,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  tff(u12,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  tff(u11,negated_conjecture,
% 0.21/0.51      ~r1_orders_2(sK0,sK1,k4_yellow_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  % (3660)# SZS output end Saturation.
% 0.21/0.51  % (3660)------------------------------
% 0.21/0.51  % (3660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3660)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (3660)Memory used [KB]: 5245
% 0.21/0.51  % (3660)Time elapsed: 0.070 s
% 0.21/0.51  % (3660)------------------------------
% 0.21/0.51  % (3660)------------------------------
% 0.21/0.52  % (3653)Success in time 0.15 s
%------------------------------------------------------------------------------
