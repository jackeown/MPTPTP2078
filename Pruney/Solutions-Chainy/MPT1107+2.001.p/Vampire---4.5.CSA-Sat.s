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
% DateTime   : Thu Dec  3 13:09:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) )).

cnf(u35,negated_conjecture,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1) )).

cnf(u22,axiom,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | ~ l1_pre_topc(X0)
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )).

cnf(u17,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X1) )).

cnf(u25,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1)) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X2)
    | ~ m1_pre_topc(X2,X0)
    | k1_pre_topc(X0,k2_struct_0(X2)) = X2 )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k1_pre_topc(X0,X1)) )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | m1_pre_topc(k1_pre_topc(X0,X1),X0) )).

cnf(u33,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) )).

cnf(u16,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u32,negated_conjecture,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) )).

cnf(u15,negated_conjecture,
    ( sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (21745)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.13/0.41  % (21745)Refutation not found, incomplete strategy% (21745)------------------------------
% 0.13/0.41  % (21745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (21745)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.41  
% 0.13/0.41  % (21745)Memory used [KB]: 1535
% 0.13/0.41  % (21745)Time elapsed: 0.002 s
% 0.13/0.41  % (21745)------------------------------
% 0.13/0.41  % (21745)------------------------------
% 0.20/0.44  % (21746)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (21739)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (21733)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21733)Refutation not found, incomplete strategy% (21733)------------------------------
% 0.20/0.49  % (21733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21733)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21733)Memory used [KB]: 10490
% 0.20/0.49  % (21733)Time elapsed: 0.081 s
% 0.20/0.49  % (21733)------------------------------
% 0.20/0.49  % (21733)------------------------------
% 0.20/0.49  % (21741)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (21750)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (21744)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21749)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (21744)Refutation not found, incomplete strategy% (21744)------------------------------
% 0.20/0.49  % (21744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21744)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21744)Memory used [KB]: 6012
% 0.20/0.49  % (21744)Time elapsed: 0.088 s
% 0.20/0.49  % (21744)------------------------------
% 0.20/0.49  % (21744)------------------------------
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (21749)# SZS output start Saturation.
% 0.20/0.49  cnf(u27,negated_conjecture,
% 0.20/0.49      m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u35,negated_conjecture,
% 0.20/0.49      ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u22,axiom,
% 0.20/0.49      ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1).
% 0.20/0.49  
% 0.20/0.49  cnf(u17,axiom,
% 0.20/0.49      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u25,negated_conjecture,
% 0.20/0.49      v1_pre_topc(k1_pre_topc(sK0,sK1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u14,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.49  
% 0.20/0.49  cnf(u23,axiom,
% 0.20/0.49      ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2).
% 0.20/0.49  
% 0.20/0.49  cnf(u20,axiom,
% 0.20/0.49      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_pre_topc(k1_pre_topc(X0,X1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u21,axiom,
% 0.20/0.49      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,X1),X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u33,negated_conjecture,
% 0.20/0.49      l1_pre_topc(k1_pre_topc(sK0,sK1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u16,negated_conjecture,
% 0.20/0.49      l1_pre_topc(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u32,negated_conjecture,
% 0.20/0.49      sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u15,negated_conjecture,
% 0.20/0.49      sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))).
% 0.20/0.49  
% 0.20/0.49  % (21749)# SZS output end Saturation.
% 0.20/0.49  % (21749)------------------------------
% 0.20/0.49  % (21749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21749)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (21749)Memory used [KB]: 1663
% 0.20/0.49  % (21749)Time elapsed: 0.082 s
% 0.20/0.49  % (21749)------------------------------
% 0.20/0.49  % (21749)------------------------------
% 0.20/0.49  % (21731)Success in time 0.137 s
%------------------------------------------------------------------------------
