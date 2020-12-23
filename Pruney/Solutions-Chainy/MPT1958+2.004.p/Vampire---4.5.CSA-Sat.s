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
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 1.29s
% Output     : Saturation 1.29s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( v7_struct_0(sK0)
    | k3_yellow_0(sK0) = k4_yellow_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u36,axiom,
    ( v2_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u57,negated_conjecture,
    ( ~ v2_yellow_0(sK0)
    | ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u35,axiom,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u61,negated_conjecture,
    ( ~ v1_yellow_0(sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X1
    | ~ r1_orders_2(sK0,X1,k3_yellow_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u38,axiom,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u37,axiom,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u64,negated_conjecture,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u69,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
    | k3_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u49,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u41,axiom,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u47,negated_conjecture,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u30,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u39,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u32,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) )).

cnf(u43,negated_conjecture,
    ( k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) )).

cnf(u42,negated_conjecture,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) )).

cnf(u28,negated_conjecture,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:43:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (1848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (1833)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (1848)Refutation not found, incomplete strategy% (1848)------------------------------
% 0.22/0.51  % (1848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1841)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (1849)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (1841)Refutation not found, incomplete strategy% (1841)------------------------------
% 0.22/0.52  % (1841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1841)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1841)Memory used [KB]: 6140
% 0.22/0.52  % (1841)Time elapsed: 0.002 s
% 0.22/0.52  % (1841)------------------------------
% 0.22/0.52  % (1841)------------------------------
% 0.22/0.52  % (1833)Refutation not found, incomplete strategy% (1833)------------------------------
% 0.22/0.52  % (1833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1848)Memory used [KB]: 10746
% 0.22/0.52  % (1848)Time elapsed: 0.095 s
% 0.22/0.52  % (1848)------------------------------
% 0.22/0.52  % (1848)------------------------------
% 0.22/0.52  % (1833)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1833)Memory used [KB]: 6268
% 0.22/0.52  % (1833)Time elapsed: 0.095 s
% 0.22/0.52  % (1833)------------------------------
% 0.22/0.52  % (1833)------------------------------
% 0.22/0.52  % (1849)Refutation not found, incomplete strategy% (1849)------------------------------
% 0.22/0.52  % (1849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1843)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (1849)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1849)Memory used [KB]: 1791
% 0.22/0.53  % (1849)Time elapsed: 0.095 s
% 0.22/0.53  % (1849)------------------------------
% 0.22/0.53  % (1849)------------------------------
% 1.29/0.53  % (1840)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (1843)Refutation not found, incomplete strategy% (1843)------------------------------
% 1.29/0.53  % (1843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (1843)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (1843)Memory used [KB]: 10618
% 1.29/0.54  % (1843)Time elapsed: 0.105 s
% 1.29/0.54  % (1843)------------------------------
% 1.29/0.54  % (1843)------------------------------
% 1.29/0.54  % (1829)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (1832)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.29/0.54  % (1832)# SZS output start Saturation.
% 1.29/0.54  cnf(u27,negated_conjecture,
% 1.29/0.54      v7_struct_0(sK0) | k3_yellow_0(sK0) = k4_yellow_0(sK0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u29,negated_conjecture,
% 1.29/0.54      ~v2_struct_0(sK0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u36,axiom,
% 1.29/0.54      v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u57,negated_conjecture,
% 1.29/0.54      ~v2_yellow_0(sK0) | ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u35,axiom,
% 1.29/0.54      v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u61,negated_conjecture,
% 1.29/0.54      ~v1_yellow_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X1 | ~r1_orders_2(sK0,X1,k3_yellow_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u31,negated_conjecture,
% 1.29/0.54      v3_yellow_0(sK0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u38,axiom,
% 1.29/0.54      r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u37,axiom,
% 1.29/0.54      r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u64,negated_conjecture,
% 1.29/0.54      ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u69,negated_conjecture,
% 1.29/0.54      ~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | k3_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u49,negated_conjecture,
% 1.29/0.54      ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1).
% 1.29/0.54  
% 1.29/0.54  cnf(u41,axiom,
% 1.29/0.54      m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u47,negated_conjecture,
% 1.29/0.54      m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u40,axiom,
% 1.29/0.54      m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u45,negated_conjecture,
% 1.29/0.54      m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))).
% 1.29/0.54  
% 1.29/0.54  cnf(u30,negated_conjecture,
% 1.29/0.54      v5_orders_2(sK0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u39,axiom,
% 1.29/0.54      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 1.29/0.54  
% 1.29/0.54  cnf(u32,negated_conjecture,
% 1.29/0.54      l1_orders_2(sK0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u33,axiom,
% 1.29/0.54      ~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u34,axiom,
% 1.29/0.54      ~l1_orders_2(X0) | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u43,negated_conjecture,
% 1.29/0.54      k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u42,negated_conjecture,
% 1.29/0.54      k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)).
% 1.29/0.54  
% 1.29/0.54  cnf(u28,negated_conjecture,
% 1.29/0.54      k3_yellow_0(sK0) != k4_yellow_0(sK0) | ~v7_struct_0(sK0)).
% 1.29/0.54  
% 1.29/0.54  % (1832)# SZS output end Saturation.
% 1.29/0.54  % (1832)------------------------------
% 1.29/0.54  % (1832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (1832)Termination reason: Satisfiable
% 1.29/0.54  
% 1.29/0.54  % (1832)Memory used [KB]: 6268
% 1.29/0.54  % (1832)Time elapsed: 0.124 s
% 1.29/0.54  % (1832)------------------------------
% 1.29/0.54  % (1832)------------------------------
% 1.29/0.54  % (1855)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (1845)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (1836)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.55  % (1834)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (1836)Refutation not found, incomplete strategy% (1836)------------------------------
% 1.29/0.55  % (1836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (1836)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (1836)Memory used [KB]: 10618
% 1.29/0.55  % (1836)Time elapsed: 0.134 s
% 1.29/0.55  % (1836)------------------------------
% 1.29/0.55  % (1836)------------------------------
% 1.29/0.55  % (1846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.55  % (1847)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.55  % (1830)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (1855)Refutation not found, incomplete strategy% (1855)------------------------------
% 1.45/0.55  % (1855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (1855)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (1855)Memory used [KB]: 1791
% 1.45/0.55  % (1855)Time elapsed: 0.128 s
% 1.45/0.55  % (1855)------------------------------
% 1.45/0.55  % (1855)------------------------------
% 1.45/0.55  % (1844)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (1826)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.55  % (1826)Refutation not found, incomplete strategy% (1826)------------------------------
% 1.45/0.55  % (1826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (1837)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (1854)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (1842)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (1853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (1851)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.55  % (1831)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (1839)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (1853)Refutation not found, incomplete strategy% (1853)------------------------------
% 1.45/0.56  % (1853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (1853)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (1853)Memory used [KB]: 6268
% 1.45/0.56  % (1853)Time elapsed: 0.139 s
% 1.45/0.56  % (1853)------------------------------
% 1.45/0.56  % (1853)------------------------------
% 1.45/0.56  % (1831)Refutation not found, incomplete strategy% (1831)------------------------------
% 1.45/0.56  % (1831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (1828)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.56  % (1825)Success in time 0.198 s
%------------------------------------------------------------------------------
