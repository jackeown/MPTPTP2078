%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   63 (  63 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( v7_struct_0(sK0)
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v7_struct_0(sK0)
    | k4_yellow_0(sK0) != k3_yellow_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u50,negated_conjecture,
    ( v2_yellow_0(sK0) )).

cnf(u48,negated_conjecture,
    ( v1_yellow_0(sK0) )).

cnf(u31,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u36,axiom,
    ( ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v1_yellow_0(X0) )).

cnf(u37,axiom,
    ( ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_yellow_0(X0) )).

cnf(u30,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u69,negated_conjecture,
    ( r1_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0)) )).

cnf(u63,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0)) )).

cnf(u43,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_orders_2(X0,X2,X1) )).

cnf(u40,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | r2_orders_2(X0,X1,X2) )).

cnf(u78,negated_conjecture,
    ( r2_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

cnf(u82,negated_conjecture,
    ( ~ r2_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0)) )).

cnf(u38,axiom,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u45,axiom,
    ( ~ r2_orders_2(X0,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u52,negated_conjecture,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u51,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,k4_yellow_0(X0)) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,k3_yellow_0(X0),X1) )).

cnf(u32,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) )).

cnf(u35,axiom,
    ( ~ l1_orders_2(X0)
    | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) )).

cnf(u53,negated_conjecture,
    ( k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (14949)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (14949)Refutation not found, incomplete strategy% (14949)------------------------------
% 0.21/0.47  % (14949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14949)Memory used [KB]: 6140
% 0.21/0.47  % (14949)Time elapsed: 0.006 s
% 0.21/0.47  % (14949)------------------------------
% 0.21/0.47  % (14949)------------------------------
% 0.21/0.47  % (14934)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (14950)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (14934)Refutation not found, incomplete strategy% (14934)------------------------------
% 0.21/0.47  % (14934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14934)Memory used [KB]: 6140
% 0.21/0.47  % (14934)Time elapsed: 0.059 s
% 0.21/0.47  % (14934)------------------------------
% 0.21/0.47  % (14934)------------------------------
% 0.21/0.47  % (14952)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (14942)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (14952)Refutation not found, incomplete strategy% (14952)------------------------------
% 0.21/0.47  % (14952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14952)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14952)Memory used [KB]: 1663
% 0.21/0.47  % (14952)Time elapsed: 0.064 s
% 0.21/0.47  % (14952)------------------------------
% 0.21/0.47  % (14952)------------------------------
% 0.21/0.47  % (14950)Refutation not found, incomplete strategy% (14950)------------------------------
% 0.21/0.47  % (14950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14950)Memory used [KB]: 10746
% 0.21/0.47  % (14950)Time elapsed: 0.030 s
% 0.21/0.47  % (14950)------------------------------
% 0.21/0.47  % (14950)------------------------------
% 0.21/0.47  % (14945)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (14945)Refutation not found, incomplete strategy% (14945)------------------------------
% 0.21/0.48  % (14945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14945)Memory used [KB]: 10618
% 0.21/0.48  % (14945)Time elapsed: 0.064 s
% 0.21/0.48  % (14945)------------------------------
% 0.21/0.48  % (14945)------------------------------
% 0.21/0.48  % (14935)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14937)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (14935)Refutation not found, incomplete strategy% (14935)------------------------------
% 0.21/0.48  % (14935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14935)Memory used [KB]: 10618
% 0.21/0.48  % (14935)Time elapsed: 0.072 s
% 0.21/0.48  % (14935)------------------------------
% 0.21/0.48  % (14935)------------------------------
% 0.21/0.48  % (14938)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (14937)Refutation not found, incomplete strategy% (14937)------------------------------
% 0.21/0.48  % (14937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14937)Memory used [KB]: 10618
% 0.21/0.48  % (14937)Time elapsed: 0.077 s
% 0.21/0.48  % (14937)------------------------------
% 0.21/0.48  % (14937)------------------------------
% 0.21/0.48  % (14936)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (14941)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (14938)Refutation not found, incomplete strategy% (14938)------------------------------
% 0.21/0.48  % (14938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14938)Memory used [KB]: 1663
% 0.21/0.48  % (14938)Time elapsed: 0.083 s
% 0.21/0.48  % (14938)------------------------------
% 0.21/0.48  % (14938)------------------------------
% 0.21/0.48  % (14953)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (14936)Refutation not found, incomplete strategy% (14936)------------------------------
% 0.21/0.48  % (14936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14936)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14936)Memory used [KB]: 10618
% 0.21/0.48  % (14936)Time elapsed: 0.077 s
% 0.21/0.48  % (14936)------------------------------
% 0.21/0.48  % (14936)------------------------------
% 0.21/0.48  % (14947)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (14947)Refutation not found, incomplete strategy% (14947)------------------------------
% 0.21/0.48  % (14947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14947)Memory used [KB]: 1663
% 0.21/0.48  % (14947)Time elapsed: 0.079 s
% 0.21/0.48  % (14947)------------------------------
% 0.21/0.48  % (14947)------------------------------
% 0.21/0.48  % (14953)Refutation not found, incomplete strategy% (14953)------------------------------
% 0.21/0.48  % (14953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14953)Memory used [KB]: 6140
% 0.21/0.48  % (14953)Time elapsed: 0.086 s
% 0.21/0.48  % (14953)------------------------------
% 0.21/0.48  % (14953)------------------------------
% 0.21/0.48  % (14946)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14951)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (14946)Refutation not found, incomplete strategy% (14946)------------------------------
% 0.21/0.48  % (14946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14946)Memory used [KB]: 6012
% 0.21/0.48  % (14946)Time elapsed: 0.002 s
% 0.21/0.49  % (14946)------------------------------
% 0.21/0.49  % (14946)------------------------------
% 0.21/0.49  % (14940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (14951)# SZS output start Saturation.
% 0.21/0.49  cnf(u27,negated_conjecture,
% 0.21/0.49      v7_struct_0(sK0) | k4_yellow_0(sK0) = k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,negated_conjecture,
% 0.21/0.49      ~v7_struct_0(sK0) | k4_yellow_0(sK0) != k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u50,negated_conjecture,
% 0.21/0.49      v2_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u48,negated_conjecture,
% 0.21/0.49      v1_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,negated_conjecture,
% 0.21/0.49      v3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u36,axiom,
% 0.21/0.49      ~v3_yellow_0(X0) | ~l1_orders_2(X0) | v1_yellow_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,axiom,
% 0.21/0.49      ~v3_yellow_0(X0) | ~l1_orders_2(X0) | v2_yellow_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,negated_conjecture,
% 0.21/0.49      v5_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u69,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u63,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u59,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u43,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u40,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u78,negated_conjecture,
% 0.21/0.49      r2_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) | k4_yellow_0(sK0) = k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u82,negated_conjecture,
% 0.21/0.49      ~r2_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u38,axiom,
% 0.21/0.49      ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u45,axiom,
% 0.21/0.49      ~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u52,negated_conjecture,
% 0.21/0.49      m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u51,negated_conjecture,
% 0.21/0.49      m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u41,axiom,
% 0.21/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,k4_yellow_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,axiom,
% 0.21/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u53,negated_conjecture,
% 0.21/0.49      k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  % (14951)# SZS output end Saturation.
% 0.21/0.49  % (14951)------------------------------
% 0.21/0.49  % (14951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14951)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (14951)Memory used [KB]: 1663
% 0.21/0.49  % (14951)Time elapsed: 0.078 s
% 0.21/0.49  % (14939)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14951)------------------------------
% 0.21/0.49  % (14951)------------------------------
% 0.21/0.49  % (14933)Success in time 0.132 s
%------------------------------------------------------------------------------
