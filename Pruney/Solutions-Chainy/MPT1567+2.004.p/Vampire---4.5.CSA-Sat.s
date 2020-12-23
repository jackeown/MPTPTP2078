%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u41,axiom,
    ( sP4(sK3(sK3(X0))) )).

cnf(u40,axiom,
    ( sP4(k1_xboole_0) )).

cnf(u39,axiom,
    ( ~ sP4(X1)
    | ~ r2_hidden(X0,X1) )).

cnf(u33,axiom,
    ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u28,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u60,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u51,negated_conjecture,
    ( r1_lattice3(sK0,sK3(sK3(X0)),sK1) )).

cnf(u45,negated_conjecture,
    ( r1_lattice3(sK0,k1_xboole_0,sK1) )).

cnf(u30,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u48,axiom,
    ( ~ r2_hidden(X0,sK3(sK3(X1))) )).

cnf(u43,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u65,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u68,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u35,axiom,
    ( v1_xboole_0(sK3(X0)) )).

cnf(u38,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sP4(X1) )).

cnf(u34,axiom,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )).

cnf(u29,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u47,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(X1)))
    | sP4(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14942)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (14934)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (14934)Refutation not found, incomplete strategy% (14934)------------------------------
% 0.21/0.49  % (14934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14934)Memory used [KB]: 895
% 0.21/0.49  % (14934)Time elapsed: 0.072 s
% 0.21/0.49  % (14934)------------------------------
% 0.21/0.49  % (14934)------------------------------
% 0.21/0.49  % (14931)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (14944)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (14944)Refutation not found, incomplete strategy% (14944)------------------------------
% 0.21/0.49  % (14944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14944)Memory used [KB]: 895
% 0.21/0.49  % (14944)Time elapsed: 0.036 s
% 0.21/0.49  % (14944)------------------------------
% 0.21/0.49  % (14944)------------------------------
% 0.21/0.49  % (14939)WARNING: option uwaf not known.
% 0.21/0.49  % (14939)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % (14940)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.50  % (14935)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.50  % (14947)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (14933)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (14932)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.50  % (14941)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (14943)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  % (14932)Refutation not found, incomplete strategy% (14932)------------------------------
% 0.21/0.50  % (14932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14932)Memory used [KB]: 9850
% 0.21/0.50  % (14932)Time elapsed: 0.092 s
% 0.21/0.50  % (14932)------------------------------
% 0.21/0.50  % (14932)------------------------------
% 0.21/0.50  % (14943)Refutation not found, incomplete strategy% (14943)------------------------------
% 0.21/0.50  % (14943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14943)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14943)Memory used [KB]: 5373
% 0.21/0.50  % (14943)Time elapsed: 0.092 s
% 0.21/0.50  % (14943)------------------------------
% 0.21/0.50  % (14943)------------------------------
% 0.21/0.51  % (14945)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.51  % (14948)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.51  % (14929)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (14936)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.51  % (14929)Refutation not found, incomplete strategy% (14929)------------------------------
% 0.21/0.51  % (14929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14929)Memory used [KB]: 5373
% 0.21/0.51  % (14929)Time elapsed: 0.091 s
% 0.21/0.51  % (14929)------------------------------
% 0.21/0.51  % (14929)------------------------------
% 0.21/0.51  % (14940)Refutation not found, incomplete strategy% (14940)------------------------------
% 0.21/0.51  % (14940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14940)Memory used [KB]: 5373
% 0.21/0.51  % (14940)Time elapsed: 0.097 s
% 0.21/0.51  % (14940)------------------------------
% 0.21/0.51  % (14940)------------------------------
% 0.21/0.51  % (14946)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.51  % (14949)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.52  % (14942)Refutation not found, incomplete strategy% (14942)------------------------------
% 0.21/0.52  % (14942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14942)Memory used [KB]: 5373
% 0.21/0.52  % (14942)Time elapsed: 0.102 s
% 0.21/0.52  % (14942)------------------------------
% 0.21/0.52  % (14942)------------------------------
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (14949)# SZS output start Saturation.
% 0.21/0.52  cnf(u41,axiom,
% 0.21/0.52      sP4(sK3(sK3(X0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      sP4(k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u39,axiom,
% 0.21/0.52      ~sP4(X1) | ~r2_hidden(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,axiom,
% 0.21/0.52      ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u28,negated_conjecture,
% 0.21/0.52      ~r1_orders_2(sK0,sK1,k4_yellow_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u59,negated_conjecture,
% 0.21/0.52      r1_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u60,negated_conjecture,
% 0.21/0.52      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u51,negated_conjecture,
% 0.21/0.52      r1_lattice3(sK0,sK3(sK3(X0)),sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,negated_conjecture,
% 0.21/0.52      r1_lattice3(sK0,k1_xboole_0,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u30,axiom,
% 0.21/0.52      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u32,axiom,
% 0.21/0.52      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u31,axiom,
% 0.21/0.52      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      ~r2_hidden(X0,sK3(sK3(X1)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u43,axiom,
% 0.21/0.52      ~r2_hidden(X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,axiom,
% 0.21/0.52      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u65,negated_conjecture,
% 0.21/0.52      ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u68,negated_conjecture,
% 0.21/0.52      ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u35,axiom,
% 0.21/0.52      v1_xboole_0(sK3(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,axiom,
% 0.21/0.52      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      m1_subset_1(sK3(X0),k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u29,axiom,
% 0.21/0.52      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u27,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u47,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u42,axiom,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(sK3(X1))) | sP4(X0)).
% 0.21/0.52  
% 0.21/0.52  % (14949)# SZS output end Saturation.
% 0.21/0.52  % (14949)------------------------------
% 0.21/0.52  % (14949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14949)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (14949)Memory used [KB]: 5373
% 0.21/0.52  % (14949)Time elapsed: 0.107 s
% 0.21/0.52  % (14949)------------------------------
% 0.21/0.52  % (14949)------------------------------
% 0.21/0.52  % (14928)Success in time 0.153 s
%------------------------------------------------------------------------------
