%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 1.52s
% Output     : Saturation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u76,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )).

tff(u75,negated_conjecture,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) )).

tff(u74,negated_conjecture,(
    v1_relat_1(sK2) )).

tff(u73,axiom,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u72,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

tff(u71,negated_conjecture,(
    v1_funct_1(sK2) )).

tff(u70,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u69,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u68,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u67,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) )).

tff(u66,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) )).

tff(u64,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

tff(u63,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

tff(u62,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u61,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u60,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u59,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u58,negated_conjecture,
    ( ~ ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) )).

tff(u57,negated_conjecture,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

tff(u56,negated_conjecture,(
    v23_waybel_0(sK2,sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (29155)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (29167)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (29162)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (29160)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (29157)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (29166)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (29166)Refutation not found, incomplete strategy% (29166)------------------------------
% 0.21/0.51  % (29166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29166)Memory used [KB]: 1663
% 0.21/0.51  % (29166)Time elapsed: 0.068 s
% 0.21/0.51  % (29166)------------------------------
% 0.21/0.51  % (29166)------------------------------
% 0.21/0.51  % (29175)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (29175)Refutation not found, incomplete strategy% (29175)------------------------------
% 0.21/0.51  % (29175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29175)Memory used [KB]: 6012
% 0.21/0.51  % (29175)Time elapsed: 0.105 s
% 0.21/0.51  % (29175)------------------------------
% 0.21/0.51  % (29175)------------------------------
% 1.35/0.53  % (29158)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.35/0.53  % (29162)Refutation not found, incomplete strategy% (29162)------------------------------
% 1.35/0.53  % (29162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (29162)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (29162)Memory used [KB]: 6012
% 1.35/0.53  % (29162)Time elapsed: 0.091 s
% 1.35/0.53  % (29162)------------------------------
% 1.35/0.53  % (29162)------------------------------
% 1.35/0.53  % (29171)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.35/0.54  % (29171)Refutation not found, incomplete strategy% (29171)------------------------------
% 1.35/0.54  % (29171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (29171)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (29171)Memory used [KB]: 1535
% 1.35/0.54  % (29171)Time elapsed: 0.114 s
% 1.35/0.54  % (29171)------------------------------
% 1.35/0.54  % (29171)------------------------------
% 1.35/0.54  % (29165)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.35/0.54  % (29164)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.35/0.54  % (29174)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.35/0.54  % (29165)Refutation not found, incomplete strategy% (29165)------------------------------
% 1.35/0.54  % (29165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (29165)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (29165)Memory used [KB]: 10618
% 1.35/0.54  % (29165)Time elapsed: 0.107 s
% 1.35/0.54  % (29165)------------------------------
% 1.35/0.54  % (29165)------------------------------
% 1.35/0.54  % (29173)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.52/0.55  % (29176)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.52/0.55  % (29176)Refutation not found, incomplete strategy% (29176)------------------------------
% 1.52/0.55  % (29176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (29176)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (29176)Memory used [KB]: 1663
% 1.52/0.55  % (29176)Time elapsed: 0.139 s
% 1.52/0.55  % (29176)------------------------------
% 1.52/0.55  % (29176)------------------------------
% 1.52/0.55  % (29158)Refutation not found, incomplete strategy% (29158)------------------------------
% 1.52/0.55  % (29158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (29158)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (29158)Memory used [KB]: 10490
% 1.52/0.55  % (29158)Time elapsed: 0.133 s
% 1.52/0.55  % (29158)------------------------------
% 1.52/0.55  % (29158)------------------------------
% 1.52/0.55  % (29159)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.52/0.55  % (29178)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.52/0.55  % (29177)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.52/0.55  % (29178)Refutation not found, incomplete strategy% (29178)------------------------------
% 1.52/0.55  % (29178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (29178)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (29178)Memory used [KB]: 10618
% 1.52/0.55  % (29178)Time elapsed: 0.143 s
% 1.52/0.55  % (29178)------------------------------
% 1.52/0.55  % (29178)------------------------------
% 1.52/0.56  % (29168)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.52/0.56  % (29169)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.52/0.56  % (29156)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.52/0.56  % SZS status CounterSatisfiable for theBenchmark
% 1.52/0.56  % (29169)# SZS output start Saturation.
% 1.52/0.56  tff(u76,negated_conjecture,
% 1.52/0.56      ((~(u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)))) | (u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))))).
% 1.52/0.56  
% 1.52/0.56  tff(u75,negated_conjecture,
% 1.52/0.56      (k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2))).
% 1.52/0.56  
% 1.52/0.56  tff(u74,negated_conjecture,
% 1.52/0.56      v1_relat_1(sK2)).
% 1.52/0.56  
% 1.52/0.56  tff(u73,axiom,
% 1.52/0.56      (![X0] : ((v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 1.52/0.56  
% 1.52/0.56  tff(u72,negated_conjecture,
% 1.52/0.56      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)))).
% 1.52/0.56  
% 1.52/0.56  tff(u71,negated_conjecture,
% 1.52/0.56      v1_funct_1(sK2)).
% 1.52/0.56  
% 1.52/0.56  tff(u70,axiom,
% 1.52/0.56      (![X0] : ((~v2_funct_1(X0) | (k2_funct_1(k2_funct_1(X0)) = X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 1.52/0.56  
% 1.52/0.56  tff(u69,axiom,
% 1.52/0.56      (![X0] : ((~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 1.52/0.56  
% 1.52/0.56  tff(u68,axiom,
% 1.52/0.56      (![X0] : ((~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 1.52/0.56  
% 1.52/0.56  tff(u67,negated_conjecture,
% 1.52/0.56      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2))).
% 1.52/0.56  
% 1.52/0.56  tff(u66,axiom,
% 1.52/0.56      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2)))))).
% 1.52/0.56  
% 1.52/0.56  tff(u65,axiom,
% 1.52/0.56      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))))).
% 1.52/0.56  
% 1.52/0.56  tff(u64,negated_conjecture,
% 1.52/0.56      ((~~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))).
% 1.52/0.56  
% 1.52/0.56  tff(u63,negated_conjecture,
% 1.52/0.56      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 1.52/0.56  
% 1.52/0.56  tff(u62,negated_conjecture,
% 1.52/0.56      ~v2_struct_0(sK0)).
% 1.52/0.56  
% 1.52/0.56  tff(u61,negated_conjecture,
% 1.52/0.56      ~v2_struct_0(sK1)).
% 1.52/0.56  
% 1.52/0.56  tff(u60,negated_conjecture,
% 1.52/0.56      l1_orders_2(sK0)).
% 1.52/0.56  
% 1.52/0.56  tff(u59,negated_conjecture,
% 1.52/0.56      l1_orders_2(sK1)).
% 1.52/0.56  
% 1.52/0.56  tff(u58,negated_conjecture,
% 1.52/0.56      ((~~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)))).
% 1.52/0.56  
% 1.52/0.56  tff(u57,negated_conjecture,
% 1.52/0.56      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 1.52/0.56  
% 1.52/0.56  tff(u56,negated_conjecture,
% 1.52/0.56      v23_waybel_0(sK2,sK0,sK1)).
% 1.52/0.56  
% 1.52/0.56  % (29169)# SZS output end Saturation.
% 1.52/0.56  % (29169)------------------------------
% 1.52/0.56  % (29169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (29169)Termination reason: Satisfiable
% 1.52/0.56  
% 1.52/0.56  % (29169)Memory used [KB]: 10618
% 1.52/0.56  % (29169)Time elapsed: 0.081 s
% 1.52/0.56  % (29169)------------------------------
% 1.52/0.56  % (29169)------------------------------
% 1.52/0.56  % (29154)Success in time 0.201 s
%------------------------------------------------------------------------------
