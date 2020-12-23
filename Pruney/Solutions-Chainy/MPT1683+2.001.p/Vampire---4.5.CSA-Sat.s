%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   44 (  44 expanded)
%              Depth                    :    0
%              Number of atoms          :  152 ( 152 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u183,negated_conjecture,(
    ~ v1_xboole_0(sK1) )).

tff(u182,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) )).

tff(u181,negated_conjecture,(
    ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u180,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) )).

tff(u179,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u178,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | v1_xboole_0(X0) ) )).

tff(u177,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_xboole_0(X0) ) )).

tff(u176,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) ) )).

tff(u175,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u174,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u173,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u172,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v5_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u171,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v5_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u170,axiom,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u169,axiom,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u168,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u167,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
      | ~ r2_hidden(X5,u1_struct_0(X1))
      | r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u166,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))),u1_struct_0(X1))
      | v5_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u165,axiom,(
    ! [X1,X0] :
      ( ~ v2_struct_0(X1)
      | v1_xboole_0(X0)
      | ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) )).

tff(u164,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u163,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u162,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u161,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u160,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u159,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u158,axiom,(
    ! [X5,X4,X6] :
      ( ~ m1_yellow_0(X6,X5)
      | k7_domain_1(u1_struct_0(X5),sK3(X5,X6),X4) = k2_tarski(sK3(X5,X6),X4)
      | v1_xboole_0(u1_struct_0(X5))
      | v5_yellow_0(X6,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | v2_struct_0(X5) ) )).

tff(u157,axiom,(
    ! [X1,X3,X2] :
      ( ~ m1_yellow_0(X3,X2)
      | k7_domain_1(u1_struct_0(X2),sK2(X2,X3),X1) = k2_tarski(sK2(X2,X3),X1)
      | v1_xboole_0(u1_struct_0(X2))
      | v5_yellow_0(X3,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) )).

tff(u156,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r2_hidden(sK3(X0,X1),u1_struct_0(X1))
      | v5_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u155,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r2_hidden(sK2(X0,X1),u1_struct_0(X1))
      | v5_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u154,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_yellow_0(X3,sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK0,X3),X2)) = k12_lattice3(sK0,sK3(sK0,X3),X2)
      | v5_yellow_0(X3,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u153,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK2(sK0,X1),X0)) = k12_lattice3(sK0,sK2(sK0,X1),X0)
      | v5_yellow_0(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u152,negated_conjecture,
    ( ~ ~ v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | ~ v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) )).

tff(u151,axiom,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0)))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u150,negated_conjecture,(
    ! [X1,X0] :
      ( r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u149,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1)))
      | v5_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u148,axiom,(
    ! [X9,X10] :
      ( ~ v5_orders_2(X10)
      | k7_domain_1(u1_struct_0(X10),sK5(X10),X9) = k2_tarski(sK5(X10),X9)
      | v1_xboole_0(u1_struct_0(X10))
      | v2_lattice3(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) )).

tff(u147,axiom,(
    ! [X7,X8] :
      ( ~ v5_orders_2(X8)
      | k7_domain_1(u1_struct_0(X8),sK4(X8),X7) = k2_tarski(sK4(X8),X7)
      | v1_xboole_0(u1_struct_0(X8))
      | v2_lattice3(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X8)) ) )).

tff(u146,axiom,(
    ! [X3,X0,X4] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X3,X4)) ) )).

tff(u145,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u144,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u143,axiom,(
    ! [X1,X0,X2] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u142,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u141,negated_conjecture,(
    v13_waybel_0(sK1,sK0) )).

tff(u140,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | v2_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (19384)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (19378)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (19382)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (19384)Refutation not found, incomplete strategy% (19384)------------------------------
% 0.22/0.51  % (19384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19381)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (19401)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (19388)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (19381)Refutation not found, incomplete strategy% (19381)------------------------------
% 0.22/0.51  % (19381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19393)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (19394)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (19396)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (19380)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (19398)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (19388)Refutation not found, incomplete strategy% (19388)------------------------------
% 0.22/0.51  % (19388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19388)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19388)Memory used [KB]: 10618
% 0.22/0.51  % (19388)Time elapsed: 0.092 s
% 0.22/0.51  % (19388)------------------------------
% 0.22/0.51  % (19388)------------------------------
% 0.22/0.51  % (19401)Refutation not found, incomplete strategy% (19401)------------------------------
% 0.22/0.51  % (19401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19389)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (19381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19381)Memory used [KB]: 10618
% 0.22/0.51  % (19381)Time elapsed: 0.093 s
% 0.22/0.51  % (19381)------------------------------
% 0.22/0.51  % (19381)------------------------------
% 0.22/0.51  % (19392)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (19384)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19384)Memory used [KB]: 10618
% 0.22/0.51  % (19384)Time elapsed: 0.093 s
% 0.22/0.51  % (19384)------------------------------
% 0.22/0.51  % (19384)------------------------------
% 0.22/0.51  % (19400)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (19380)Refutation not found, incomplete strategy% (19380)------------------------------
% 0.22/0.52  % (19380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19380)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  % (19383)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  
% 0.22/0.52  % (19380)Memory used [KB]: 10618
% 0.22/0.52  % (19380)Time elapsed: 0.104 s
% 0.22/0.52  % (19380)------------------------------
% 0.22/0.52  % (19380)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (19398)Refutation not found, incomplete strategy% (19398)------------------------------
% 0.22/0.52  % (19398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19398)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19398)Memory used [KB]: 6140
% 0.22/0.52  % (19398)Time elapsed: 0.107 s
% 0.22/0.52  % (19398)------------------------------
% 0.22/0.52  % (19398)------------------------------
% 0.22/0.52  % (19399)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (19392)# SZS output start Saturation.
% 0.22/0.52  tff(u183,negated_conjecture,
% 0.22/0.52      ~v1_xboole_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u182,axiom,
% 0.22/0.52      (![X1, X0] : ((~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u181,negated_conjecture,
% 0.22/0.52      ~v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u180,axiom,
% 0.22/0.52      (![X0] : ((v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u179,negated_conjecture,
% 0.22/0.52      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u178,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)) | v1_xboole_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u177,negated_conjecture,
% 0.22/0.52      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u176,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u175,negated_conjecture,
% 0.22/0.52      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u174,negated_conjecture,
% 0.22/0.52      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u173,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u172,axiom,
% 0.22/0.52      (![X1, X0] : ((m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u171,axiom,
% 0.22/0.52      (![X1, X0] : ((m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u170,axiom,
% 0.22/0.52      (![X0] : ((m1_subset_1(sK4(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u169,axiom,
% 0.22/0.52      (![X0] : ((m1_subset_1(sK5(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u168,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u167,axiom,
% 0.22/0.52      (![X1, X5, X0, X4] : ((~r2_hidden(X4,u1_struct_0(X1)) | ~r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)) | ~r2_hidden(X5,u1_struct_0(X1)) | r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u166,axiom,
% 0.22/0.52      (![X1, X0] : ((~r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u165,axiom,
% 0.22/0.52      (![X1, X0] : ((~v2_struct_0(X1) | v1_xboole_0(X0) | ~l1_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))))))).
% 0.22/0.52  
% 0.22/0.52  tff(u164,axiom,
% 0.22/0.52      (![X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u163,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u162,negated_conjecture,
% 0.22/0.52      l1_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u161,axiom,
% 0.22/0.52      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u160,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u159,negated_conjecture,
% 0.22/0.52      v2_lattice3(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u158,axiom,
% 0.22/0.52      (![X5, X4, X6] : ((~m1_yellow_0(X6,X5) | (k7_domain_1(u1_struct_0(X5),sK3(X5,X6),X4) = k2_tarski(sK3(X5,X6),X4)) | v1_xboole_0(u1_struct_0(X5)) | v5_yellow_0(X6,X5) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~l1_orders_2(X5) | v2_struct_0(X5))))).
% 0.22/0.52  
% 0.22/0.52  tff(u157,axiom,
% 0.22/0.52      (![X1, X3, X2] : ((~m1_yellow_0(X3,X2) | (k7_domain_1(u1_struct_0(X2),sK2(X2,X3),X1) = k2_tarski(sK2(X2,X3),X1)) | v1_xboole_0(u1_struct_0(X2)) | v5_yellow_0(X3,X2) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l1_orders_2(X2) | v2_struct_0(X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u156,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r2_hidden(sK3(X0,X1),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u155,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r2_hidden(sK2(X0,X1),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u154,negated_conjecture,
% 0.22/0.52      (![X3, X2] : ((~m1_yellow_0(X3,sK0) | (k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK0,X3),X2)) = k12_lattice3(sK0,sK3(sK0,X3),X2)) | v5_yellow_0(X3,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u153,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((~m1_yellow_0(X1,sK0) | (k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK2(sK0,X1),X0)) = k12_lattice3(sK0,sK2(sK0,X1),X0)) | v5_yellow_0(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u152,negated_conjecture,
% 0.22/0.52      ((~~v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)) | ~v5_yellow_0(k5_yellow_0(sK0,sK1),sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u151,axiom,
% 0.22/0.52      (![X0] : ((~r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0))) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u150,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((r2_yellow_0(sK0,k2_tarski(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u149,axiom,
% 0.22/0.52      (![X1, X0] : ((r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u148,axiom,
% 0.22/0.52      (![X9, X10] : ((~v5_orders_2(X10) | (k7_domain_1(u1_struct_0(X10),sK5(X10),X9) = k2_tarski(sK5(X10),X9)) | v1_xboole_0(u1_struct_0(X10)) | v2_lattice3(X10) | ~l1_orders_2(X10) | ~m1_subset_1(X9,u1_struct_0(X10)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u147,axiom,
% 0.22/0.52      (![X7, X8] : ((~v5_orders_2(X8) | (k7_domain_1(u1_struct_0(X8),sK4(X8),X7) = k2_tarski(sK4(X8),X7)) | v1_xboole_0(u1_struct_0(X8)) | v2_lattice3(X8) | ~l1_orders_2(X8) | ~m1_subset_1(X7,u1_struct_0(X8)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u146,axiom,
% 0.22/0.52      (![X3, X0, X4] : ((~v5_orders_2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | r2_yellow_0(X0,k2_tarski(X3,X4)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u145,negated_conjecture,
% 0.22/0.52      v5_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u144,negated_conjecture,
% 0.22/0.52      v3_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u143,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~v4_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | (k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u142,negated_conjecture,
% 0.22/0.52      v4_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u141,negated_conjecture,
% 0.22/0.52      v13_waybel_0(sK1,sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u140,negated_conjecture,
% 0.22/0.52      ((~v2_waybel_0(sK1,sK0)) | v2_waybel_0(sK1,sK0))).
% 0.22/0.52  
% 0.22/0.52  % (19392)# SZS output end Saturation.
% 0.22/0.52  % (19392)------------------------------
% 0.22/0.52  % (19392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19392)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (19392)Memory used [KB]: 10746
% 0.22/0.52  % (19392)Time elapsed: 0.111 s
% 0.22/0.52  % (19392)------------------------------
% 0.22/0.52  % (19392)------------------------------
% 0.22/0.52  % (19377)Success in time 0.159 s
%------------------------------------------------------------------------------
