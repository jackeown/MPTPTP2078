%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u10,negated_conjecture,
    ( v1_yellow_0(sK0) )).

cnf(u9,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u8,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (341)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (349)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.46  % (349)Refutation not found, incomplete strategy% (349)------------------------------
% 0.21/0.46  % (349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (335)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.46  % (349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (349)Memory used [KB]: 5245
% 0.21/0.46  % (349)Time elapsed: 0.056 s
% 0.21/0.46  % (349)------------------------------
% 0.21/0.46  % (349)------------------------------
% 0.21/0.46  % (347)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % (339)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (347)# SZS output start Saturation.
% 0.21/0.46  cnf(u13,negated_conjecture,
% 0.21/0.46      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u12,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u11,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u10,negated_conjecture,
% 0.21/0.46      v1_yellow_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u9,negated_conjecture,
% 0.21/0.46      v5_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u8,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  % (347)# SZS output end Saturation.
% 0.21/0.46  % (347)------------------------------
% 0.21/0.46  % (347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (347)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (347)Memory used [KB]: 5245
% 0.21/0.46  % (347)Time elapsed: 0.005 s
% 0.21/0.46  % (347)------------------------------
% 0.21/0.46  % (347)------------------------------
% 0.21/0.46  % (332)Success in time 0.112 s
%------------------------------------------------------------------------------
