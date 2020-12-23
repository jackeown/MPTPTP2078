%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

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
    ( ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u10,negated_conjecture,
    ( v2_yellow_0(sK0) )).

cnf(u9,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u8,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (20304)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (20304)# SZS output start Saturation.
% 0.21/0.42  cnf(u13,negated_conjecture,
% 0.21/0.42      ~r1_orders_2(sK0,sK1,k4_yellow_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  cnf(u12,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  cnf(u11,negated_conjecture,
% 0.21/0.42      l1_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u10,negated_conjecture,
% 0.21/0.42      v2_yellow_0(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u9,negated_conjecture,
% 0.21/0.42      v5_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u8,negated_conjecture,
% 0.21/0.42      ~v2_struct_0(sK0)).
% 0.21/0.42  
% 0.21/0.42  % (20304)# SZS output end Saturation.
% 0.21/0.42  % (20304)------------------------------
% 0.21/0.42  % (20304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20304)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (20304)Memory used [KB]: 5245
% 0.21/0.42  % (20304)Time elapsed: 0.003 s
% 0.21/0.42  % (20304)------------------------------
% 0.21/0.42  % (20304)------------------------------
% 0.21/0.42  % (20288)Success in time 0.061 s
%------------------------------------------------------------------------------
