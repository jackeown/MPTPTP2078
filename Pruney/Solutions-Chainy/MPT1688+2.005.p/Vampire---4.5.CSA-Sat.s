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
% DateTime   : Thu Dec  3 13:17:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u70,negated_conjecture,(
    k2_funct_1(sK2) = sK3 )).

tff(u69,axiom,(
    ! [X1,X0] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) )).

tff(u68,axiom,(
    ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) )).

tff(u67,negated_conjecture,(
    v1_relat_1(sK2) )).

tff(u66,negated_conjecture,(
    v1_relat_1(sK3) )).

tff(u65,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | v1_relat_1(X0) ) )).

tff(u64,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
      | v1_relat_1(X0) ) )).

tff(u63,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) )).

tff(u62,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

tff(u61,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

tff(u60,negated_conjecture,(
    v1_funct_1(sK2) )).

tff(u59,negated_conjecture,(
    v1_funct_1(sK3) )).

tff(u58,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u57,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u56,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u55,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u54,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u53,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u52,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u51,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u50,negated_conjecture,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

tff(u49,negated_conjecture,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) )).

tff(u48,negated_conjecture,(
    ~ v23_waybel_0(sK3,sK1,sK0) )).

tff(u47,negated_conjecture,(
    v23_waybel_0(sK2,sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (6175)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (6165)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (6165)Refutation not found, incomplete strategy% (6165)------------------------------
% 0.21/0.49  % (6165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6165)Memory used [KB]: 10490
% 0.21/0.49  % (6165)Time elapsed: 0.062 s
% 0.21/0.49  % (6165)------------------------------
% 0.21/0.49  % (6165)------------------------------
% 0.21/0.50  % (6175)Refutation not found, incomplete strategy% (6175)------------------------------
% 0.21/0.50  % (6175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6175)Memory used [KB]: 6012
% 0.21/0.50  % (6175)Time elapsed: 0.064 s
% 0.21/0.50  % (6175)------------------------------
% 0.21/0.50  % (6175)------------------------------
% 0.21/0.51  % (6159)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (6157)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (6155)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (6177)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (6169)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (6169)# SZS output start Saturation.
% 0.21/0.52  tff(u70,negated_conjecture,
% 0.21/0.52      (k2_funct_1(sK2) = sK3)).
% 0.21/0.52  
% 0.21/0.52  tff(u69,axiom,
% 0.21/0.52      (![X1, X0] : ((~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u68,axiom,
% 0.21/0.52      (![X1, X0] : (v1_relat_1(k2_zfmisc_1(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u67,negated_conjecture,
% 0.21/0.52      v1_relat_1(sK2)).
% 0.21/0.52  
% 0.21/0.52  tff(u66,negated_conjecture,
% 0.21/0.52      v1_relat_1(sK3)).
% 0.21/0.52  
% 0.21/0.52  tff(u65,negated_conjecture,
% 0.21/0.52      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u64,negated_conjecture,
% 0.21/0.52      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(sK3)) | v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u63,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u62,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u61,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u60,negated_conjecture,
% 0.21/0.52      v1_funct_1(sK2)).
% 0.21/0.52  
% 0.21/0.52  tff(u59,negated_conjecture,
% 0.21/0.52      v1_funct_1(sK3)).
% 0.21/0.52  
% 0.21/0.52  tff(u58,axiom,
% 0.21/0.52      (![X0] : ((~v2_funct_1(X0) | (k2_funct_1(k2_funct_1(X0)) = X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u57,axiom,
% 0.21/0.52      (![X0] : ((~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u56,axiom,
% 0.21/0.52      (![X0] : ((~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u55,axiom,
% 0.21/0.52      (![X0] : ((~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u54,negated_conjecture,
% 0.21/0.52      ~v2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  tff(u53,negated_conjecture,
% 0.21/0.52      ~v2_struct_0(sK1)).
% 0.21/0.52  
% 0.21/0.52  tff(u52,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  tff(u51,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK1)).
% 0.21/0.52  
% 0.21/0.52  tff(u50,negated_conjecture,
% 0.21/0.52      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.52  
% 0.21/0.52  tff(u49,negated_conjecture,
% 0.21/0.52      v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  tff(u48,negated_conjecture,
% 0.21/0.52      ~v23_waybel_0(sK3,sK1,sK0)).
% 0.21/0.52  
% 0.21/0.52  tff(u47,negated_conjecture,
% 0.21/0.52      v23_waybel_0(sK2,sK0,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (6169)# SZS output end Saturation.
% 0.21/0.52  % (6169)------------------------------
% 0.21/0.52  % (6169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6169)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (6169)Memory used [KB]: 10618
% 0.21/0.52  % (6169)Time elapsed: 0.051 s
% 0.21/0.52  % (6169)------------------------------
% 0.21/0.52  % (6169)------------------------------
% 0.21/0.52  % (6166)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (6167)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (6154)Success in time 0.16 s
%------------------------------------------------------------------------------
