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
% DateTime   : Thu Dec  3 13:17:13 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u58,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u57,negated_conjecture,(
    sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u56,negated_conjecture,(
    sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u55,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u54,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u53,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u51,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u50,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u48,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u47,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u46,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u45,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u44,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31475)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (31484)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (31483)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (31471)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (31474)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (31471)Refutation not found, incomplete strategy% (31471)------------------------------
% 0.21/0.51  % (31471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31477)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (31480)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (31484)Refutation not found, incomplete strategy% (31484)------------------------------
% 0.21/0.51  % (31484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31484)Memory used [KB]: 6140
% 0.21/0.51  % (31484)Time elapsed: 0.091 s
% 0.21/0.51  % (31484)------------------------------
% 0.21/0.51  % (31484)------------------------------
% 0.21/0.51  % (31468)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (31475)Refutation not found, incomplete strategy% (31475)------------------------------
% 0.21/0.51  % (31475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31475)Memory used [KB]: 10490
% 0.21/0.51  % (31475)Time elapsed: 0.003 s
% 0.21/0.51  % (31475)------------------------------
% 0.21/0.51  % (31475)------------------------------
% 0.21/0.51  % (31476)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (31476)Refutation not found, incomplete strategy% (31476)------------------------------
% 0.21/0.51  % (31476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (31468)Refutation not found, incomplete strategy% (31468)------------------------------
% 0.21/0.51  % (31468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31468)Memory used [KB]: 10490
% 0.21/0.51  % (31468)Time elapsed: 0.095 s
% 0.21/0.51  % (31468)------------------------------
% 0.21/0.51  % (31468)------------------------------
% 0.21/0.51  % (31476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31476)Memory used [KB]: 1663
% 0.21/0.51  % (31476)Time elapsed: 0.093 s
% 0.21/0.51  % (31476)------------------------------
% 0.21/0.51  % (31476)------------------------------
% 0.21/0.52  % (31485)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (31471)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31471)Memory used [KB]: 10618
% 0.21/0.52  % (31471)Time elapsed: 0.085 s
% 0.21/0.52  % (31471)------------------------------
% 0.21/0.52  % (31471)------------------------------
% 0.21/0.52  % (31469)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.18/0.52  % (31482)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.18/0.52  % (31482)Refutation not found, incomplete strategy% (31482)------------------------------
% 1.18/0.52  % (31482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (31482)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (31482)Memory used [KB]: 1663
% 1.18/0.52  % (31482)Time elapsed: 0.098 s
% 1.18/0.52  % (31482)------------------------------
% 1.18/0.52  % (31482)------------------------------
% 1.18/0.52  % (31470)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.18/0.52  % (31478)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.18/0.52  % (31466)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.18/0.52  % (31467)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.18/0.52  % (31487)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.18/0.52  % (31465)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.18/0.53  % (31472)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.18/0.53  % (31472)Refutation not found, incomplete strategy% (31472)------------------------------
% 1.18/0.53  % (31472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (31472)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (31472)Memory used [KB]: 6012
% 1.18/0.53  % (31472)Time elapsed: 0.002 s
% 1.18/0.53  % (31472)------------------------------
% 1.18/0.53  % (31472)------------------------------
% 1.18/0.53  % (31481)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.18/0.53  % (31481)Refutation not found, incomplete strategy% (31481)------------------------------
% 1.18/0.53  % (31481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (31481)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (31481)Memory used [KB]: 1535
% 1.18/0.53  % (31481)Time elapsed: 0.001 s
% 1.18/0.53  % (31481)------------------------------
% 1.18/0.53  % (31481)------------------------------
% 1.18/0.53  % (31477)# SZS output start Saturation.
% 1.18/0.53  tff(u58,negated_conjecture,
% 1.18/0.53      ((~(sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))) | (sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))))).
% 1.18/0.53  
% 1.18/0.53  tff(u57,negated_conjecture,
% 1.18/0.53      (sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 1.18/0.53  
% 1.18/0.53  tff(u56,negated_conjecture,
% 1.18/0.53      (sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 1.18/0.53  
% 1.18/0.53  tff(u55,negated_conjecture,
% 1.18/0.53      ~v2_struct_0(sK0)).
% 1.18/0.53  
% 1.18/0.53  tff(u54,axiom,
% 1.18/0.53      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 1.18/0.53  
% 1.18/0.53  tff(u53,axiom,
% 1.18/0.53      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 1.18/0.53  
% 1.18/0.53  tff(u52,axiom,
% 1.18/0.53      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 1.18/0.53  
% 1.18/0.53  tff(u51,axiom,
% 1.18/0.53      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 1.18/0.53  
% 1.18/0.53  tff(u50,negated_conjecture,
% 1.18/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.18/0.53  
% 1.18/0.53  tff(u49,axiom,
% 1.18/0.53      (![X1, X0] : ((m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 1.18/0.53  
% 1.18/0.53  tff(u48,negated_conjecture,
% 1.18/0.53      l1_orders_2(sK0)).
% 1.18/0.53  
% 1.18/0.53  tff(u47,negated_conjecture,
% 1.18/0.53      v3_orders_2(sK0)).
% 1.18/0.53  
% 1.18/0.53  tff(u46,negated_conjecture,
% 1.18/0.53      v5_orders_2(sK0)).
% 1.18/0.53  
% 1.18/0.53  tff(u45,negated_conjecture,
% 1.18/0.53      ((~~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))).
% 1.18/0.53  
% 1.18/0.53  tff(u44,axiom,
% 1.18/0.53      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 1.18/0.53  
% 1.18/0.53  % (31477)# SZS output end Saturation.
% 1.18/0.53  % (31477)------------------------------
% 1.18/0.53  % (31477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (31477)Termination reason: Satisfiable
% 1.18/0.53  
% 1.18/0.53  % (31477)Memory used [KB]: 10618
% 1.18/0.53  % (31477)Time elapsed: 0.101 s
% 1.18/0.53  % (31477)------------------------------
% 1.18/0.53  % (31477)------------------------------
% 1.18/0.53  % (31464)Success in time 0.163 s
%------------------------------------------------------------------------------
