%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:24 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( v23_waybel_0(sK2,sK0,sK1) )).

cnf(u18,negated_conjecture,
    ( ~ v23_waybel_0(sK3,sK1,sK0) )).

cnf(u20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u15,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u24,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u23,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u28,axiom,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u29,axiom,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 )).

cnf(u37,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | v2_funct_1(sK3) )).

cnf(u43,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) )).

cnf(u19,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u14,negated_conjecture,
    ( v1_funct_1(sK3) )).

cnf(u38,axiom,
    ( ~ v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(k2_funct_1(X0))
    | k2_funct_1(X0) = k2_funct_1(k2_funct_1(k2_funct_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u34,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u33,negated_conjecture,
    ( v1_relat_1(sK3) )).

cnf(u30,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u17,negated_conjecture,
    ( sK3 = k2_funct_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (28907)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (28903)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (28901)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (28901)Refutation not found, incomplete strategy% (28901)------------------------------
% 0.22/0.50  % (28901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28901)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28901)Memory used [KB]: 10490
% 0.22/0.50  % (28901)Time elapsed: 0.087 s
% 0.22/0.50  % (28921)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (28901)------------------------------
% 0.22/0.50  % (28901)------------------------------
% 0.22/0.50  % (28913)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (28921)Refutation not found, incomplete strategy% (28921)------------------------------
% 0.22/0.50  % (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28917)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (28917)Refutation not found, incomplete strategy% (28917)------------------------------
% 0.22/0.51  % (28917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28909)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (28904)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (28917)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28917)Memory used [KB]: 6140
% 0.22/0.51  % (28917)Time elapsed: 0.089 s
% 0.22/0.51  % (28917)------------------------------
% 0.22/0.51  % (28917)------------------------------
% 0.22/0.51  % (28909)Refutation not found, incomplete strategy% (28909)------------------------------
% 0.22/0.51  % (28909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28909)Memory used [KB]: 1663
% 0.22/0.51  % (28909)Time elapsed: 0.090 s
% 0.22/0.51  % (28909)------------------------------
% 0.22/0.51  % (28909)------------------------------
% 0.22/0.51  % (28919)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (28904)Refutation not found, incomplete strategy% (28904)------------------------------
% 0.22/0.51  % (28904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28904)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28904)Memory used [KB]: 10618
% 0.22/0.51  % (28904)Time elapsed: 0.095 s
% 0.22/0.51  % (28904)------------------------------
% 0.22/0.51  % (28904)------------------------------
% 0.22/0.51  % (28919)Refutation not found, incomplete strategy% (28919)------------------------------
% 0.22/0.51  % (28919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28919)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28919)Memory used [KB]: 1663
% 0.22/0.51  % (28919)Time elapsed: 0.099 s
% 0.22/0.51  % (28919)------------------------------
% 0.22/0.51  % (28919)------------------------------
% 0.22/0.51  % (28898)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (28911)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (28908)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (28906)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (28911)# SZS output start Saturation.
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      v23_waybel_0(sK2,sK0,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,negated_conjecture,
% 0.22/0.51      ~v23_waybel_0(sK3,sK1,sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,negated_conjecture,
% 0.22/0.51      v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,axiom,
% 0.22/0.51      v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,axiom,
% 0.22/0.51      ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,negated_conjecture,
% 0.22/0.51      ~v2_funct_1(sK2) | v2_funct_1(sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,negated_conjecture,
% 0.22/0.51      ~v2_funct_1(sK2) | sK3 = k2_funct_1(k2_funct_1(sK3))).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,negated_conjecture,
% 0.22/0.51      v1_funct_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u14,negated_conjecture,
% 0.22/0.51      v1_funct_1(sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | k2_funct_1(X0) = k2_funct_1(k2_funct_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,negated_conjecture,
% 0.22/0.51      v1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,negated_conjecture,
% 0.22/0.51      v1_relat_1(sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,negated_conjecture,
% 0.22/0.51      sK3 = k2_funct_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  % (28911)# SZS output end Saturation.
% 0.22/0.51  % (28911)------------------------------
% 0.22/0.51  % (28911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28911)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (28911)Memory used [KB]: 6140
% 0.22/0.51  % (28911)Time elapsed: 0.101 s
% 0.22/0.51  % (28911)------------------------------
% 0.22/0.51  % (28911)------------------------------
% 0.22/0.51  % (28908)Refutation not found, incomplete strategy% (28908)------------------------------
% 0.22/0.51  % (28908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28908)Memory used [KB]: 10490
% 0.22/0.51  % (28908)Time elapsed: 0.095 s
% 0.22/0.51  % (28908)------------------------------
% 0.22/0.51  % (28908)------------------------------
% 0.22/0.51  % (28897)Success in time 0.152 s
%------------------------------------------------------------------------------
