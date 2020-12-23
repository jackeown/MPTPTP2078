%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 1.53s
% Output     : Saturation 1.53s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :  140 ( 140 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,axiom,
    ( v6_orders_2(sK2(X0,X1,X2),X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,X1)
    | ~ v3_orders_2(X0) )).

cnf(u34,axiom,
    ( v6_orders_2(sK2(X0,X1,X2),X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0) )).

cnf(u25,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u29,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u47,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u82,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,X0,sK1)) = k2_tarski(sK2(sK0,X0,sK1),sK2(sK0,X0,sK1)) )).

cnf(u50,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,sK1)
    | sK1 = X0 )).

cnf(u54,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u28,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,X1)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u38,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_orders_2(X4,X0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X2,X1) )).

cnf(u74,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(X0)),sK2(X0,X1,X2)) = k2_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2)) )).

cnf(u24,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u23,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u58,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k2_tarski(sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) )).

cnf(u40,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u35,axiom,
    ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0) )).

cnf(u56,negated_conjecture,
    ( m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u73,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k2_tarski(sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ r2_hidden(X1,X0) )).

cnf(u46,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u49,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | X0 = X1 )).

cnf(u53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X1,X0)
    | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v6_orders_2(X2,sK0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2)
    | r1_orders_2(sK0,X0,X1)
    | r1_orders_2(sK0,X1,X0) )).

cnf(u77,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v6_orders_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X1)
    | ~ r2_hidden(X0,X1)
    | r1_orders_2(sK0,sK1,X0)
    | r1_orders_2(sK0,X0,sK1) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,X0,X1)) = k2_tarski(sK2(sK0,X0,X1),sK2(sK0,X0,X1)) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1) )).

cnf(u33,axiom,
    ( r2_hidden(X2,sK2(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,X1)
    | ~ v3_orders_2(X0) )).

cnf(u37,axiom,
    ( r2_hidden(X2,sK2(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0) )).

cnf(u32,axiom,
    ( r2_hidden(X1,sK2(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,X1)
    | ~ v3_orders_2(X0) )).

cnf(u36,axiom,
    ( r2_hidden(X1,sK2(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0) )).

cnf(u70,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u72,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (818)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (818)Refutation not found, incomplete strategy% (818)------------------------------
% 0.21/0.56  % (818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (818)Memory used [KB]: 10746
% 0.21/0.57  % (818)Time elapsed: 0.130 s
% 0.21/0.57  % (818)------------------------------
% 0.21/0.57  % (818)------------------------------
% 0.21/0.57  % (815)Refutation not found, incomplete strategy% (815)------------------------------
% 0.21/0.57  % (815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (815)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (815)Memory used [KB]: 1663
% 0.21/0.57  % (815)Time elapsed: 0.133 s
% 0.21/0.57  % (815)------------------------------
% 0.21/0.57  % (815)------------------------------
% 1.53/0.57  % (820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.57  % (826)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (816)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.58  % (820)Refutation not found, incomplete strategy% (820)------------------------------
% 1.53/0.58  % (820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (820)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (820)Memory used [KB]: 6268
% 1.53/0.58  % (820)Time elapsed: 0.148 s
% 1.53/0.58  % (820)------------------------------
% 1.53/0.58  % (820)------------------------------
% 1.53/0.58  % (817)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (826)Refutation not found, incomplete strategy% (826)------------------------------
% 1.53/0.58  % (826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.58  % (826)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (826)Memory used [KB]: 10618
% 1.53/0.58  % (826)Time elapsed: 0.141 s
% 1.53/0.58  % (826)------------------------------
% 1.53/0.58  % (826)------------------------------
% 1.53/0.58  % (817)Refutation not found, incomplete strategy% (817)------------------------------
% 1.53/0.58  % (817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (817)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (817)Memory used [KB]: 10618
% 1.53/0.58  % (817)Time elapsed: 0.144 s
% 1.53/0.58  % (817)------------------------------
% 1.53/0.58  % (817)------------------------------
% 1.53/0.58  % (843)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.53/0.58  % (821)# SZS output start Saturation.
% 1.53/0.58  cnf(u30,axiom,
% 1.53/0.58      v6_orders_2(sK2(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u34,axiom,
% 1.53/0.58      v6_orders_2(sK2(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u25,negated_conjecture,
% 1.53/0.58      v5_orders_2(sK0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u29,axiom,
% 1.53/0.58      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 1.53/0.58  
% 1.53/0.58  cnf(u47,negated_conjecture,
% 1.53/0.58      r1_orders_2(sK0,sK1,sK1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u82,negated_conjecture,
% 1.53/0.58      ~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,X0,sK1)) = k2_tarski(sK2(sK0,X0,sK1),sK2(sK0,X0,sK1))).
% 1.53/0.58  
% 1.53/0.58  cnf(u50,negated_conjecture,
% 1.53/0.58      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1) | sK1 = X0).
% 1.53/0.58  
% 1.53/0.58  cnf(u54,negated_conjecture,
% 1.53/0.58      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.53/0.58  
% 1.53/0.58  cnf(u26,negated_conjecture,
% 1.53/0.58      l1_orders_2(sK0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u28,axiom,
% 1.53/0.58      ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u31,axiom,
% 1.53/0.58      ~l1_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))).
% 1.53/0.58  
% 1.53/0.58  cnf(u38,axiom,
% 1.53/0.58      ~l1_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v6_orders_2(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X4) | r1_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u74,axiom,
% 1.53/0.58      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(X0)),sK2(X0,X1,X2)) = k2_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2))).
% 1.53/0.58  
% 1.53/0.58  cnf(u24,negated_conjecture,
% 1.53/0.58      v3_orders_2(sK0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u23,negated_conjecture,
% 1.53/0.58      ~v2_struct_0(sK0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u58,negated_conjecture,
% 1.53/0.58      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k2_tarski(sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))).
% 1.53/0.58  
% 1.53/0.58  cnf(u40,axiom,
% 1.53/0.58      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u35,axiom,
% 1.53/0.58      m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u56,negated_conjecture,
% 1.53/0.58      m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.53/0.58  
% 1.53/0.58  cnf(u22,negated_conjecture,
% 1.53/0.58      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.53/0.58  
% 1.53/0.58  cnf(u73,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k2_tarski(sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | ~r2_hidden(X1,X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u46,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u49,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 1.53/0.58  
% 1.53/0.58  cnf(u53,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.53/0.58  
% 1.53/0.58  cnf(u76,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v6_orders_2(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X1,X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u77,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_orders_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X1) | ~r2_hidden(X0,X1) | r1_orders_2(sK0,sK1,X0) | r1_orders_2(sK0,X0,sK1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u81,negated_conjecture,
% 1.53/0.58      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,X0,X1)) = k2_tarski(sK2(sK0,X0,X1),sK2(sK0,X0,X1))).
% 1.53/0.58  
% 1.53/0.58  cnf(u41,axiom,
% 1.53/0.58      ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u33,axiom,
% 1.53/0.58      r2_hidden(X2,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u37,axiom,
% 1.53/0.58      r2_hidden(X2,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u32,axiom,
% 1.53/0.58      r2_hidden(X1,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u36,axiom,
% 1.53/0.58      r2_hidden(X1,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0)).
% 1.53/0.58  
% 1.53/0.58  cnf(u70,negated_conjecture,
% 1.53/0.58      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 1.53/0.58  
% 1.53/0.58  cnf(u72,negated_conjecture,
% 1.53/0.58      sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 1.53/0.58  
% 1.53/0.58  % (821)# SZS output end Saturation.
% 1.53/0.58  % (821)------------------------------
% 1.53/0.58  % (821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (821)Termination reason: Satisfiable
% 1.53/0.58  
% 1.53/0.58  % (821)Memory used [KB]: 6268
% 1.53/0.58  % (821)Time elapsed: 0.143 s
% 1.53/0.58  % (821)------------------------------
% 1.53/0.58  % (821)------------------------------
% 1.53/0.58  % (814)Success in time 0.215 s
%------------------------------------------------------------------------------
