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
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :    7 (   7 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u7,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK2) )).

cnf(u6,negated_conjecture,
    ( r1_lattice3(sK0,sK1,sK2) )).

cnf(u8,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK1,sK3) )).

cnf(u9,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u5,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u10,negated_conjecture,
    ( v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (26408)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (26414)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (26414)# SZS output start Saturation.
% 0.22/0.47  cnf(u7,negated_conjecture,
% 0.22/0.47      r1_orders_2(sK0,sK3,sK2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u6,negated_conjecture,
% 0.22/0.47      r1_lattice3(sK0,sK1,sK2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u8,negated_conjecture,
% 0.22/0.47      ~r1_lattice3(sK0,sK1,sK3)).
% 0.22/0.47  
% 0.22/0.47  cnf(u9,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u5,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u11,negated_conjecture,
% 0.22/0.47      l1_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u10,negated_conjecture,
% 0.22/0.47      v4_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  % (26414)# SZS output end Saturation.
% 0.22/0.47  % (26414)------------------------------
% 0.22/0.47  % (26414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26414)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (26414)Memory used [KB]: 767
% 0.22/0.47  % (26414)Time elapsed: 0.005 s
% 0.22/0.47  % (26414)------------------------------
% 0.22/0.47  % (26414)------------------------------
% 0.22/0.47  % (26398)Success in time 0.109 s
%------------------------------------------------------------------------------
