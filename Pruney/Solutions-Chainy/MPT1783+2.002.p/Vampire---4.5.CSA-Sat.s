%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   81 (  81 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u120,negated_conjecture,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) )).

tff(u119,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u118,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u117,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u116,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u115,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) )).

tff(u114,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u113,axiom,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u112,axiom,(
    ! [X1,X0] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) )).

tff(u111,axiom,(
    ! [X1,X3,X0,X2] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) )).

tff(u110,axiom,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u109,axiom,(
    ! [X1,X0] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) )).

tff(u108,axiom,(
    ! [X1,X3,X0,X2] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) )).

tff(u107,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u106,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) )).

tff(u105,negated_conjecture,
    ( ~ ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)
    | ~ v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0) )).

tff(u104,axiom,(
    ! [X0] :
      ( v5_pre_topc(k3_struct_0(X0),X0,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u103,axiom,(
    ! [X1,X3,X0,X2] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:31:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (30989)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (30994)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (30986)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (30999)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (31000)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.50  % (30984)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (31003)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.50  % (31006)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (30988)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (30983)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (30998)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (30994)Refutation not found, incomplete strategy% (30994)------------------------------
% 0.22/0.51  % (30994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31006)Refutation not found, incomplete strategy% (31006)------------------------------
% 0.22/0.51  % (31006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30991)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (30986)Refutation not found, incomplete strategy% (30986)------------------------------
% 0.22/0.51  % (30986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31006)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31006)Memory used [KB]: 10618
% 0.22/0.51  % (31006)Time elapsed: 0.047 s
% 0.22/0.51  % (31006)------------------------------
% 0.22/0.51  % (31006)------------------------------
% 0.22/0.51  % (31000)Refutation not found, incomplete strategy% (31000)------------------------------
% 0.22/0.51  % (31000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31000)Memory used [KB]: 1663
% 0.22/0.51  % (31000)Time elapsed: 0.099 s
% 0.22/0.51  % (31000)------------------------------
% 0.22/0.51  % (31000)------------------------------
% 0.22/0.51  % (30990)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (30987)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (30995)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (31002)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (30986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30986)Memory used [KB]: 10618
% 0.22/0.51  % (30986)Time elapsed: 0.098 s
% 0.22/0.51  % (30986)------------------------------
% 0.22/0.51  % (30986)------------------------------
% 0.22/0.51  % (30990)Refutation not found, incomplete strategy% (30990)------------------------------
% 0.22/0.51  % (30990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30990)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30990)Memory used [KB]: 6012
% 0.22/0.51  % (30990)Time elapsed: 0.004 s
% 0.22/0.51  % (30990)------------------------------
% 0.22/0.51  % (30990)------------------------------
% 0.22/0.51  % (30992)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (30993)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (30996)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (30993)Refutation not found, incomplete strategy% (30993)------------------------------
% 0.22/0.52  % (30993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30993)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30993)Memory used [KB]: 10490
% 0.22/0.52  % (30993)Time elapsed: 0.002 s
% 0.22/0.52  % (30993)------------------------------
% 0.22/0.52  % (30993)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (30995)# SZS output start Saturation.
% 0.22/0.52  tff(u120,negated_conjecture,
% 0.22/0.52      (k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u119,negated_conjecture,
% 0.22/0.52      l1_pre_topc(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u118,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u117,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u116,negated_conjecture,
% 0.22/0.52      v2_pre_topc(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u115,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | (k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u114,negated_conjecture,
% 0.22/0.52      m1_pre_topc(sK1,sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u113,axiom,
% 0.22/0.52      (![X0] : ((v1_funct_1(k3_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u112,axiom,
% 0.22/0.52      (![X1, X0] : ((v1_funct_1(k4_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u111,axiom,
% 0.22/0.52      (![X1, X3, X0, X2] : ((v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u110,axiom,
% 0.22/0.52      (![X0] : ((v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u109,axiom,
% 0.22/0.52      (![X1, X0] : ((v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u108,axiom,
% 0.22/0.52      (![X1, X3, X0, X2] : ((v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u107,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u106,axiom,
% 0.22/0.52      (![X1, X0] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u105,negated_conjecture,
% 0.22/0.52      ((~~v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0)) | ~v5_pre_topc(k4_tmap_1(sK0,sK1),sK1,sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u104,axiom,
% 0.22/0.52      (![X0] : ((v5_pre_topc(k3_struct_0(X0),X0,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u103,axiom,
% 0.22/0.52      (![X1, X3, X0, X2] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  % (30995)# SZS output end Saturation.
% 0.22/0.52  % (30995)------------------------------
% 0.22/0.52  % (30995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30995)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (30995)Memory used [KB]: 10618
% 0.22/0.52  % (30995)Time elapsed: 0.101 s
% 0.22/0.52  % (30995)------------------------------
% 0.22/0.52  % (30995)------------------------------
% 0.22/0.52  % (31002)Refutation not found, incomplete strategy% (31002)------------------------------
% 0.22/0.52  % (31002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31002)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31002)Memory used [KB]: 6140
% 0.22/0.52  % (31002)Time elapsed: 0.102 s
% 0.22/0.52  % (31002)------------------------------
% 0.22/0.52  % (31002)------------------------------
% 0.22/0.52  % (30982)Success in time 0.153 s
%------------------------------------------------------------------------------
