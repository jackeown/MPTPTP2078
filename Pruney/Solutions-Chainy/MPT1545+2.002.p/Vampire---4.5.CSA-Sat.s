%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:59 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK3)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u17,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK2)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u16,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK1)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r1_orders_2(sK0,X4,sK2)
    | ~ r1_orders_2(sK0,X4,sK1)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,X4,sK3)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u15,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK4,sK3)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK4,sK1)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u14,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK4,sK2)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u38,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK3,X0) = k11_lattice3(sK0,sK3,X0) )).

cnf(u41,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,sK2,X1) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK1,X2) = k11_lattice3(sK0,sK1,X2) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK3,X0) = k12_lattice3(sK0,X0,sK3) )).

cnf(u53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK2,X1) = k12_lattice3(sK0,X1,sK2) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k12_lattice3(sK0,sK1,X2) = k12_lattice3(sK0,X2,sK1) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u21,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u70,negated_conjecture,
    ( k11_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3) )).

cnf(u69,negated_conjecture,
    ( k11_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3) )).

cnf(u73,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) )).

cnf(u68,negated_conjecture,
    ( k12_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3) )).

cnf(u67,negated_conjecture,
    ( k12_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3) )).

cnf(u65,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK1) = k11_lattice3(sK0,sK1,sK1) )).

cnf(u74,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1) )).

cnf(u64,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2) )).

cnf(u61,negated_conjecture,
    ( k12_lattice3(sK0,sK2,sK2) = k11_lattice3(sK0,sK2,sK2) )).

cnf(u63,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK3) = k11_lattice3(sK0,sK1,sK3) )).

cnf(u60,negated_conjecture,
    ( k12_lattice3(sK0,sK2,sK3) = k11_lattice3(sK0,sK2,sK3) )).

cnf(u57,negated_conjecture,
    ( k12_lattice3(sK0,sK3,sK3) = k11_lattice3(sK0,sK3,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (28829)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (28830)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (28830)Refutation not found, incomplete strategy% (28830)------------------------------
% 0.22/0.47  % (28830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28837)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (28830)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28830)Memory used [KB]: 10618
% 0.22/0.48  % (28830)Time elapsed: 0.048 s
% 0.22/0.48  % (28830)------------------------------
% 0.22/0.48  % (28830)------------------------------
% 0.22/0.48  % (28837)Refutation not found, incomplete strategy% (28837)------------------------------
% 0.22/0.48  % (28837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28837)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28837)Memory used [KB]: 1663
% 0.22/0.48  % (28837)Time elapsed: 0.062 s
% 0.22/0.48  % (28837)------------------------------
% 0.22/0.48  % (28837)------------------------------
% 0.22/0.48  % (28843)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (28843)Refutation not found, incomplete strategy% (28843)------------------------------
% 0.22/0.49  % (28843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28843)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28843)Memory used [KB]: 6140
% 0.22/0.49  % (28843)Time elapsed: 0.062 s
% 0.22/0.49  % (28843)------------------------------
% 0.22/0.49  % (28843)------------------------------
% 0.22/0.50  % (28832)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (28824)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (28827)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (28828)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (28839)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (28839)Refutation not found, incomplete strategy% (28839)------------------------------
% 0.22/0.51  % (28839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28839)Memory used [KB]: 6140
% 0.22/0.51  % (28839)Time elapsed: 0.093 s
% 0.22/0.51  % (28839)------------------------------
% 0.22/0.51  % (28839)------------------------------
% 0.22/0.51  % (28844)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (28841)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (28824)Refutation not found, incomplete strategy% (28824)------------------------------
% 0.22/0.51  % (28824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28824)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28824)Memory used [KB]: 6140
% 0.22/0.51  % (28824)Time elapsed: 0.082 s
% 0.22/0.51  % (28824)------------------------------
% 0.22/0.51  % (28824)------------------------------
% 0.22/0.51  % (28842)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (28844)Refutation not found, incomplete strategy% (28844)------------------------------
% 0.22/0.51  % (28844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28844)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28844)Memory used [KB]: 10618
% 0.22/0.51  % (28844)Time elapsed: 0.093 s
% 0.22/0.51  % (28844)------------------------------
% 0.22/0.51  % (28844)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (28841)# SZS output start Saturation.
% 0.22/0.51  cnf(u32,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK3,sK3) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK3,sK2) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK3,sK1) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u11,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,X4,sK2) | ~r1_orders_2(sK0,X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,X4,sK3) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,sK4,sK3) | ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u12,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | m1_subset_1(sK4,u1_struct_0(sK0)) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u13,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | r1_orders_2(sK0,sK4,sK1) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u14,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | r1_orders_2(sK0,sK4,sK2) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK3,X0) = k11_lattice3(sK0,sK3,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,sK2,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X2,u1_struct_0(sK0)) | k12_lattice3(sK0,sK1,X2) = k11_lattice3(sK0,sK1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u50,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK3,X0) = k12_lattice3(sK0,X0,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X1) = k12_lattice3(sK0,X1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X2,u1_struct_0(sK0)) | k12_lattice3(sK0,sK1,X2) = k12_lattice3(sK0,X2,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,axiom,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      v2_lattice3(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      v5_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u70,negated_conjecture,
% 0.22/0.51      k11_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u69,negated_conjecture,
% 0.22/0.51      k11_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u73,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u68,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u67,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u65,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK1,sK1) = k11_lattice3(sK0,sK1,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u74,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u64,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK2,sK2) = k11_lattice3(sK0,sK2,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u63,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK1,sK3) = k11_lattice3(sK0,sK1,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u60,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK2,sK3) = k11_lattice3(sK0,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u57,negated_conjecture,
% 0.22/0.51      k12_lattice3(sK0,sK3,sK3) = k11_lattice3(sK0,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  % (28841)# SZS output end Saturation.
% 0.22/0.51  % (28841)------------------------------
% 0.22/0.51  % (28841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28841)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (28841)Memory used [KB]: 1663
% 0.22/0.51  % (28841)Time elapsed: 0.094 s
% 0.22/0.51  % (28841)------------------------------
% 0.22/0.51  % (28841)------------------------------
% 0.22/0.51  % (28842)Refutation not found, incomplete strategy% (28842)------------------------------
% 0.22/0.51  % (28842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28842)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28842)Memory used [KB]: 1663
% 0.22/0.51  % (28842)Time elapsed: 0.094 s
% 0.22/0.51  % (28842)------------------------------
% 0.22/0.51  % (28842)------------------------------
% 0.22/0.51  % (28823)Success in time 0.152 s
%------------------------------------------------------------------------------
