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
% DateTime   : Thu Dec  3 13:17:24 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26386)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
tff(u84,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )).

tff(u83,negated_conjecture,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) )).

tff(u82,axiom,(
    ! [X1,X0] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) )).

tff(u81,axiom,(
    ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) )).

tff(u80,negated_conjecture,(
    v1_relat_1(sK2) )).

tff(u79,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

tff(u78,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | v1_relat_1(X0) ) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) )).

tff(u75,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

tff(u74,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

tff(u73,negated_conjecture,(
    v1_funct_1(sK2) )).

tff(u72,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u71,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u70,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u69,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u68,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) )).

tff(u67,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u66,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u65,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u64,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u63,negated_conjecture,
    ( ~ ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) )).

tff(u62,negated_conjecture,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

tff(u61,negated_conjecture,(
    v23_waybel_0(sK2,sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (26380)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (26383)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (26381)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (26385)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (26388)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (26380)Refutation not found, incomplete strategy% (26380)------------------------------
% 0.22/0.50  % (26380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26380)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26380)Memory used [KB]: 10618
% 0.22/0.50  % (26380)Time elapsed: 0.088 s
% 0.22/0.50  % (26380)------------------------------
% 0.22/0.50  % (26380)------------------------------
% 0.22/0.50  % (26378)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (26379)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (26388)Refutation not found, incomplete strategy% (26388)------------------------------
% 0.22/0.50  % (26388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26388)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26388)Memory used [KB]: 1663
% 0.22/0.50  % (26388)Time elapsed: 0.094 s
% 0.22/0.51  % (26388)------------------------------
% 0.22/0.51  % (26388)------------------------------
% 0.22/0.51  % (26383)Refutation not found, incomplete strategy% (26383)------------------------------
% 0.22/0.51  % (26383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26383)Memory used [KB]: 10618
% 0.22/0.51  % (26383)Time elapsed: 0.086 s
% 0.22/0.51  % (26383)------------------------------
% 0.22/0.51  % (26383)------------------------------
% 0.22/0.51  % (26397)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (26382)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (26384)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (26397)Refutation not found, incomplete strategy% (26397)------------------------------
% 0.22/0.51  % (26397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26397)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26397)Memory used [KB]: 6012
% 0.22/0.51  % (26397)Time elapsed: 0.088 s
% 0.22/0.51  % (26397)------------------------------
% 0.22/0.51  % (26397)------------------------------
% 0.22/0.51  % (26384)Refutation not found, incomplete strategy% (26384)------------------------------
% 0.22/0.51  % (26384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26384)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26384)Memory used [KB]: 6140
% 0.22/0.51  % (26384)Time elapsed: 0.050 s
% 0.22/0.51  % (26384)------------------------------
% 0.22/0.51  % (26384)------------------------------
% 0.22/0.51  % (26393)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (26377)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (26392)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (26393)Refutation not found, incomplete strategy% (26393)------------------------------
% 0.22/0.51  % (26393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26393)Memory used [KB]: 1535
% 0.22/0.51  % (26393)Time elapsed: 0.096 s
% 0.22/0.51  % (26393)------------------------------
% 0.22/0.51  % (26393)------------------------------
% 0.22/0.51  % (26399)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (26391)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (26385)Refutation not found, incomplete strategy% (26385)------------------------------
% 0.22/0.52  % (26385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26385)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26385)Memory used [KB]: 10618
% 0.22/0.52  % (26385)Time elapsed: 0.093 s
% 0.22/0.52  % (26385)------------------------------
% 0.22/0.52  % (26385)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (26391)# SZS output start Saturation.
% 0.22/0.52  % (26386)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  tff(u84,negated_conjecture,
% 0.22/0.52      ((~(u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)))) | (u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u83,negated_conjecture,
% 0.22/0.52      (k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  tff(u82,axiom,
% 0.22/0.52      (![X1, X0] : ((~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u81,axiom,
% 0.22/0.52      (![X1, X0] : (v1_relat_1(k2_zfmisc_1(X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u80,negated_conjecture,
% 0.22/0.52      v1_relat_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u79,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u78,negated_conjecture,
% 0.22/0.52      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u77,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u76,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u75,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u74,negated_conjecture,
% 0.22/0.52      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)))).
% 0.22/0.52  
% 0.22/0.52  tff(u73,negated_conjecture,
% 0.22/0.52      v1_funct_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u72,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | (k2_funct_1(k2_funct_1(X0)) = X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u71,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u70,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u69,axiom,
% 0.22/0.52      (![X0] : ((~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u68,negated_conjecture,
% 0.22/0.52      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  tff(u67,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u66,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u65,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u64,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u63,negated_conjecture,
% 0.22/0.52      ((~~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u62,negated_conjecture,
% 0.22/0.52      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u61,negated_conjecture,
% 0.22/0.52      v23_waybel_0(sK2,sK0,sK1)).
% 0.22/0.52  
% 0.22/0.52  % (26391)# SZS output end Saturation.
% 0.22/0.52  % (26391)------------------------------
% 0.22/0.52  % (26391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26391)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (26398)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (26391)Memory used [KB]: 10618
% 0.22/0.52  % (26391)Time elapsed: 0.099 s
% 0.22/0.52  % (26391)------------------------------
% 0.22/0.52  % (26391)------------------------------
% 0.22/0.52  % (26376)Success in time 0.153 s
%------------------------------------------------------------------------------
