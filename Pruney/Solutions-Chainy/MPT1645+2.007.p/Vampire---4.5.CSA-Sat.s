%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u8,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) )).

cnf(u15,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK2,sK1) )).

cnf(u12,negated_conjecture,
    ( ~ v13_waybel_0(sK2,sK1)
    | v12_waybel_0(sK2,sK0) )).

cnf(u14,negated_conjecture,
    ( ~ v13_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1) )).

cnf(u11,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

cnf(u10,negated_conjecture,
    ( sK2 = sK3 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:16:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (14221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (14203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14213)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (14205)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14221)Refutation not found, incomplete strategy% (14221)------------------------------
% 0.21/0.52  % (14221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14221)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14221)Memory used [KB]: 10618
% 0.21/0.52  % (14221)Time elapsed: 0.061 s
% 0.21/0.52  % (14221)------------------------------
% 0.21/0.52  % (14221)------------------------------
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (14205)# SZS output start Saturation.
% 0.21/0.52  cnf(u8,negated_conjecture,
% 0.21/0.52      v13_waybel_0(sK2,sK0) | v12_waybel_0(sK2,sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u15,negated_conjecture,
% 0.21/0.52      v13_waybel_0(sK2,sK0) | ~v12_waybel_0(sK2,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u12,negated_conjecture,
% 0.21/0.52      ~v13_waybel_0(sK2,sK1) | v12_waybel_0(sK2,sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u14,negated_conjecture,
% 0.21/0.52      ~v13_waybel_0(sK2,sK1) | ~v12_waybel_0(sK2,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u11,negated_conjecture,
% 0.21/0.52      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u10,negated_conjecture,
% 0.21/0.52      sK2 = sK3).
% 0.21/0.52  
% 0.21/0.52  % (14205)# SZS output end Saturation.
% 0.21/0.52  % (14205)------------------------------
% 0.21/0.52  % (14205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14205)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (14205)Memory used [KB]: 6140
% 0.21/0.52  % (14205)Time elapsed: 0.065 s
% 0.21/0.52  % (14205)------------------------------
% 0.21/0.52  % (14205)------------------------------
% 0.21/0.52  % (14197)Success in time 0.161 s
%------------------------------------------------------------------------------
