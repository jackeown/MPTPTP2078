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
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u59,negated_conjecture,(
    k2_funct_1(sK2) = sK3 )).

tff(u58,negated_conjecture,(
    v1_relat_1(sK2) )).

tff(u57,negated_conjecture,(
    v1_relat_1(sK3) )).

tff(u56,negated_conjecture,(
    v1_funct_1(sK2) )).

tff(u55,negated_conjecture,(
    v1_funct_1(sK3) )).

tff(u54,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u53,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u52,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u51,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) )).

tff(u49,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

tff(u48,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

tff(u47,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u46,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u45,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u44,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u43,negated_conjecture,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

tff(u42,negated_conjecture,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) )).

tff(u41,negated_conjecture,(
    ~ v23_waybel_0(sK3,sK1,sK0) )).

tff(u40,negated_conjecture,(
    v23_waybel_0(sK2,sK0,sK1) )).

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
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13095)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (13091)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (13113)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (13110)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (13108)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (13105)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (13110)Refutation not found, incomplete strategy% (13110)------------------------------
% 0.22/0.51  % (13110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13110)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13110)Memory used [KB]: 6012
% 0.22/0.51  % (13110)Time elapsed: 0.098 s
% 0.22/0.51  % (13110)------------------------------
% 0.22/0.51  % (13110)------------------------------
% 0.22/0.51  % (13106)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (13092)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (13106)Refutation not found, incomplete strategy% (13106)------------------------------
% 0.22/0.51  % (13106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13106)Memory used [KB]: 1663
% 0.22/0.51  % (13106)Time elapsed: 0.098 s
% 0.22/0.51  % (13106)------------------------------
% 0.22/0.51  % (13106)------------------------------
% 0.22/0.51  % (13111)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (13094)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (13113)Refutation not found, incomplete strategy% (13113)------------------------------
% 0.22/0.51  % (13113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13113)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13113)Memory used [KB]: 10618
% 0.22/0.51  % (13113)Time elapsed: 0.057 s
% 0.22/0.51  % (13113)------------------------------
% 0.22/0.51  % (13113)------------------------------
% 0.22/0.51  % (13111)Refutation not found, incomplete strategy% (13111)------------------------------
% 0.22/0.51  % (13111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13111)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13111)Memory used [KB]: 1663
% 0.22/0.51  % (13111)Time elapsed: 0.100 s
% 0.22/0.51  % (13111)------------------------------
% 0.22/0.51  % (13111)------------------------------
% 0.22/0.51  % (13090)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (13096)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (13103)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (13102)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (13104)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (13104)# SZS output start Saturation.
% 0.22/0.52  tff(u59,negated_conjecture,
% 0.22/0.52      (k2_funct_1(sK2) = sK3)).
% 0.22/0.52  
% 0.22/0.52  tff(u58,negated_conjecture,
% 0.22/0.52      v1_relat_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u57,negated_conjecture,
% 0.22/0.52      v1_relat_1(sK3)).
% 0.22/0.52  
% 0.22/0.52  tff(u56,negated_conjecture,
% 0.22/0.52      v1_funct_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u55,negated_conjecture,
% 0.22/0.52      v1_funct_1(sK3)).
% 0.22/0.52  
% 0.22/0.52  tff(u54,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | (k2_funct_1(k2_funct_1(X0)) = X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u53,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u52,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u51,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u50,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u49,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u48,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u47,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u46,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u45,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u44,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u43,negated_conjecture,
% 0.22/0.52      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u42,negated_conjecture,
% 0.22/0.52      v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u41,negated_conjecture,
% 0.22/0.52      ~v23_waybel_0(sK3,sK1,sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u40,negated_conjecture,
% 0.22/0.52      v23_waybel_0(sK2,sK0,sK1)).
% 0.22/0.52  
% 0.22/0.52  % (13104)# SZS output end Saturation.
% 0.22/0.52  % (13104)------------------------------
% 0.22/0.52  % (13104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13104)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (13104)Memory used [KB]: 10618
% 0.22/0.52  % (13104)Time elapsed: 0.107 s
% 0.22/0.52  % (13104)------------------------------
% 0.22/0.52  % (13104)------------------------------
% 0.22/0.52  % (13100)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (13109)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (13089)Success in time 0.151 s
%------------------------------------------------------------------------------
