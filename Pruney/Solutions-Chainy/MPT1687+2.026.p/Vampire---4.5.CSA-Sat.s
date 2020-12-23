%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u43,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u31,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u60,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u67,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u39,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u57,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u72,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u59,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u41,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u26,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u58,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u62,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | v1_partfun1(X2,X0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u45,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u36,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u55,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (605)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (606)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (590)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (607)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (607)Refutation not found, incomplete strategy% (607)------------------------------
% 0.20/0.47  % (607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (607)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (607)Memory used [KB]: 1663
% 0.20/0.47  % (607)Time elapsed: 0.078 s
% 0.20/0.47  % (607)------------------------------
% 0.20/0.47  % (607)------------------------------
% 0.20/0.48  % (594)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (589)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (598)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (589)Refutation not found, incomplete strategy% (589)------------------------------
% 0.20/0.48  % (589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (589)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (589)Memory used [KB]: 6140
% 0.20/0.48  % (589)Time elapsed: 0.071 s
% 0.20/0.48  % (589)------------------------------
% 0.20/0.48  % (589)------------------------------
% 0.20/0.48  % (592)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (606)# SZS output start Saturation.
% 0.20/0.48  cnf(u32,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u30,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u33,axiom,
% 0.20/0.48      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u43,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u42,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u31,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u29,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u60,negated_conjecture,
% 0.20/0.48      v1_partfun1(sK2,k1_relat_1(sK2)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u67,negated_conjecture,
% 0.20/0.48      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u39,axiom,
% 0.20/0.48      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u57,negated_conjecture,
% 0.20/0.48      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u72,negated_conjecture,
% 0.20/0.48      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u35,axiom,
% 0.20/0.48      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u59,negated_conjecture,
% 0.20/0.48      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u41,axiom,
% 0.20/0.48      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u26,negated_conjecture,
% 0.20/0.48      v1_funct_1(sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u58,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.20/0.48  
% 0.20/0.48  cnf(u62,negated_conjecture,
% 0.20/0.48      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u40,axiom,
% 0.20/0.48      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u37,axiom,
% 0.20/0.48      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u34,axiom,
% 0.20/0.48      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u45,negated_conjecture,
% 0.20/0.48      v1_relat_1(sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u36,axiom,
% 0.20/0.48      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u55,negated_conjecture,
% 0.20/0.48      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.20/0.48  
% 0.20/0.48  % (606)# SZS output end Saturation.
% 0.20/0.48  % (606)------------------------------
% 0.20/0.48  % (606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (606)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (606)Memory used [KB]: 1663
% 0.20/0.48  % (606)Time elapsed: 0.082 s
% 0.20/0.48  % (606)------------------------------
% 0.20/0.48  % (606)------------------------------
% 0.20/0.48  % (592)Refutation not found, incomplete strategy% (592)------------------------------
% 0.20/0.48  % (592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (592)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (592)Memory used [KB]: 10746
% 0.20/0.48  % (592)Time elapsed: 0.074 s
% 0.20/0.48  % (592)------------------------------
% 0.20/0.48  % (592)------------------------------
% 0.20/0.48  % (588)Success in time 0.13 s
%------------------------------------------------------------------------------
