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
% DateTime   : Thu Dec  3 13:16:53 EST 2020

% Result     : CounterSatisfiable 2.23s
% Output     : Saturation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u157,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u156,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u155,negated_conjecture,
    ( sK2 != sK3
    | sK2 = sK3 )).

tff(u154,negated_conjecture,
    ( u1_struct_0(sK1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK0) )).

tff(u153,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u152,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u151,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u150,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u149,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u148,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u147,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u146,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u145,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u144,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u143,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u142,negated_conjecture,
    ( ~ ~ v2_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) )).

tff(u141,negated_conjecture,
    ( ~ v2_waybel_0(sK2,sK0)
    | v2_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (9003)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (9003)Refutation not found, incomplete strategy% (9003)------------------------------
% 0.21/0.56  % (9003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9029)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (9003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9003)Memory used [KB]: 6268
% 0.21/0.57  % (9003)Time elapsed: 0.128 s
% 0.21/0.57  % (9003)------------------------------
% 0.21/0.57  % (9003)------------------------------
% 0.21/0.57  % (9001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (9012)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (9022)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.58  % (9029)Refutation not found, incomplete strategy% (9029)------------------------------
% 0.21/0.58  % (9029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9029)Memory used [KB]: 1791
% 0.21/0.58  % (9029)Time elapsed: 0.148 s
% 0.21/0.58  % (9029)------------------------------
% 0.21/0.58  % (9029)------------------------------
% 0.21/0.58  % (9013)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.59  % (9002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (9002)Refutation not found, incomplete strategy% (9002)------------------------------
% 0.21/0.59  % (9002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (8998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.60  % (9001)Refutation not found, incomplete strategy% (9001)------------------------------
% 0.21/0.60  % (9001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (9000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.60  % (9027)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.60  % (9008)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.61  % (9009)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.61  % (9020)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  % (9009)Refutation not found, incomplete strategy% (9009)------------------------------
% 0.21/0.61  % (9009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.61  % (9022)Refutation not found, incomplete strategy% (9022)------------------------------
% 0.21/0.61  % (9022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9000)Refutation not found, incomplete strategy% (9000)------------------------------
% 0.21/0.61  % (9000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9006)Refutation not found, incomplete strategy% (9006)------------------------------
% 0.21/0.61  % (9006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (9006)Memory used [KB]: 10746
% 0.21/0.61  % (9006)Time elapsed: 0.179 s
% 0.21/0.61  % (9006)------------------------------
% 0.21/0.61  % (9006)------------------------------
% 0.21/0.61  % (9018)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (9001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (9001)Memory used [KB]: 10746
% 0.21/0.61  % (9001)Time elapsed: 0.173 s
% 0.21/0.61  % (9001)------------------------------
% 0.21/0.61  % (9001)------------------------------
% 0.21/0.61  % (9008)Refutation not found, incomplete strategy% (9008)------------------------------
% 0.21/0.61  % (9008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9011)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.61  % (9002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (9002)Memory used [KB]: 6140
% 0.21/0.61  % (9002)Time elapsed: 0.172 s
% 0.21/0.62  % (9002)------------------------------
% 0.21/0.62  % (9002)------------------------------
% 0.21/0.62  % (8998)Refutation not found, incomplete strategy% (8998)------------------------------
% 0.21/0.62  % (8998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (8998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (8998)Memory used [KB]: 1791
% 0.21/0.62  % (8998)Time elapsed: 0.188 s
% 0.21/0.62  % (8998)------------------------------
% 0.21/0.62  % (8998)------------------------------
% 0.21/0.62  % (9018)Refutation not found, incomplete strategy% (9018)------------------------------
% 0.21/0.62  % (9018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (9009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (9018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (9009)Memory used [KB]: 10746
% 0.21/0.62  % (9009)Time elapsed: 0.107 s
% 0.21/0.62  % (9018)Memory used [KB]: 10746
% 0.21/0.62  % (9009)------------------------------
% 0.21/0.62  % (9009)------------------------------
% 0.21/0.62  % (9018)Time elapsed: 0.192 s
% 0.21/0.62  % (9018)------------------------------
% 0.21/0.62  % (9018)------------------------------
% 0.21/0.62  % (9022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (9022)Memory used [KB]: 10746
% 0.21/0.62  % (9022)Time elapsed: 0.110 s
% 0.21/0.62  % (9022)------------------------------
% 0.21/0.62  % (9022)------------------------------
% 0.21/0.62  % (9028)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.62  % (9010)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.62  % (9000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (9000)Memory used [KB]: 10746
% 0.21/0.62  % (9000)Time elapsed: 0.179 s
% 0.21/0.62  % (9000)------------------------------
% 0.21/0.62  % (9000)------------------------------
% 0.21/0.62  % (9026)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.87/0.62  % (9014)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.87/0.62  % (9016)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.87/0.62  % (9027)Refutation not found, incomplete strategy% (9027)------------------------------
% 1.87/0.62  % (9027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (9027)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (9027)Memory used [KB]: 6268
% 1.87/0.62  % (9027)Time elapsed: 0.192 s
% 1.87/0.62  % (9027)------------------------------
% 1.87/0.62  % (9027)------------------------------
% 1.87/0.62  % (8999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.87/0.62  % (9008)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (9008)Memory used [KB]: 10618
% 1.87/0.62  % (9008)Time elapsed: 0.176 s
% 1.87/0.62  % (9008)------------------------------
% 1.87/0.62  % (9008)------------------------------
% 1.87/0.62  % (9017)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.87/0.62  % (9025)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.87/0.62  % (9023)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.87/0.62  % (9020)Refutation not found, incomplete strategy% (9020)------------------------------
% 1.87/0.62  % (9020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (9020)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (9020)Memory used [KB]: 1791
% 1.87/0.62  % (9020)Time elapsed: 0.193 s
% 1.87/0.62  % (9020)------------------------------
% 1.87/0.62  % (9020)------------------------------
% 1.87/0.62  % (9005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.87/0.63  % (9016)Refutation not found, incomplete strategy% (9016)------------------------------
% 1.87/0.63  % (9016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9005)Refutation not found, incomplete strategy% (9005)------------------------------
% 1.87/0.63  % (9005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9025)Refutation not found, incomplete strategy% (9025)------------------------------
% 1.87/0.63  % (9025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9014)Refutation not found, incomplete strategy% (9014)------------------------------
% 1.87/0.63  % (9014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9019)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.87/0.63  % (9004)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.87/0.63  % (9010)Refutation not found, incomplete strategy% (9010)------------------------------
% 1.87/0.63  % (9010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9016)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (9016)Memory used [KB]: 10618
% 1.87/0.63  % (9016)Time elapsed: 0.198 s
% 1.87/0.63  % (9016)------------------------------
% 1.87/0.63  % (9016)------------------------------
% 1.87/0.63  % (9023)Refutation not found, incomplete strategy% (9023)------------------------------
% 1.87/0.63  % (9023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9014)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (9014)Memory used [KB]: 6140
% 1.87/0.63  % (9014)Time elapsed: 0.197 s
% 1.87/0.63  % (9014)------------------------------
% 1.87/0.63  % (9014)------------------------------
% 1.87/0.63  % (9010)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (9010)Memory used [KB]: 10746
% 1.87/0.63  % (9010)Time elapsed: 0.201 s
% 1.87/0.63  % (9010)------------------------------
% 1.87/0.63  % (9010)------------------------------
% 1.87/0.63  % (9011)Refutation not found, incomplete strategy% (9011)------------------------------
% 1.87/0.63  % (9011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (9025)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (9025)Memory used [KB]: 6268
% 1.87/0.63  % (9025)Time elapsed: 0.199 s
% 1.87/0.63  % (9025)------------------------------
% 1.87/0.63  % (9025)------------------------------
% 1.87/0.63  % (9024)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.64  % (9019)Refutation not found, incomplete strategy% (9019)------------------------------
% 1.87/0.64  % (9019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.64  % (9011)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.64  
% 1.87/0.64  % (9011)Memory used [KB]: 6268
% 1.87/0.64  % (9011)Time elapsed: 0.202 s
% 1.87/0.64  % (9011)------------------------------
% 1.87/0.64  % (9011)------------------------------
% 1.87/0.64  % (9015)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.87/0.64  % (9019)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.64  
% 1.87/0.64  % (9019)Memory used [KB]: 10746
% 1.87/0.64  % (9019)Time elapsed: 0.212 s
% 1.87/0.64  % (9019)------------------------------
% 1.87/0.64  % (9019)------------------------------
% 1.87/0.64  % (9026)Refutation not found, incomplete strategy% (9026)------------------------------
% 1.87/0.64  % (9026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.64  % (9026)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.64  
% 1.87/0.64  % (9026)Memory used [KB]: 10746
% 1.87/0.64  % (9026)Time elapsed: 0.188 s
% 1.87/0.64  % (9026)------------------------------
% 1.87/0.64  % (9026)------------------------------
% 2.23/0.64  % (9024)Refutation not found, incomplete strategy% (9024)------------------------------
% 2.23/0.64  % (9024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.64  % (9005)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.64  
% 2.23/0.64  % (9005)Memory used [KB]: 6268
% 2.23/0.64  % (9005)Time elapsed: 0.201 s
% 2.23/0.64  % (9005)------------------------------
% 2.23/0.64  % (9005)------------------------------
% 2.23/0.64  % (9023)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.64  
% 2.23/0.64  % (9023)Memory used [KB]: 1791
% 2.23/0.64  % (9023)Time elapsed: 0.199 s
% 2.23/0.64  % (9023)------------------------------
% 2.23/0.64  % (9023)------------------------------
% 2.23/0.64  % SZS status CounterSatisfiable for theBenchmark
% 2.23/0.65  % (9024)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.65  
% 2.23/0.65  % (9024)Memory used [KB]: 6268
% 2.23/0.65  % (9024)Time elapsed: 0.209 s
% 2.23/0.65  % (9024)------------------------------
% 2.23/0.65  % (9024)------------------------------
% 2.32/0.66  % (9015)# SZS output start Saturation.
% 2.32/0.66  tff(u157,negated_conjecture,
% 2.32/0.66      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 2.32/0.66  
% 2.32/0.66  tff(u156,negated_conjecture,
% 2.32/0.66      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 2.32/0.66  
% 2.32/0.66  tff(u155,negated_conjecture,
% 2.32/0.66      ((~(sK2 = sK3)) | (sK2 = sK3))).
% 2.32/0.66  
% 2.32/0.66  tff(u154,negated_conjecture,
% 2.32/0.66      ((~(u1_struct_0(sK1) = u1_struct_0(sK0))) | (u1_struct_0(sK1) = u1_struct_0(sK0)))).
% 2.32/0.66  
% 2.32/0.66  tff(u153,negated_conjecture,
% 2.32/0.66      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 2.32/0.66  
% 2.32/0.66  tff(u152,axiom,
% 2.32/0.66      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 2.32/0.66  
% 2.32/0.66  tff(u151,negated_conjecture,
% 2.32/0.66      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 2.32/0.66  
% 2.32/0.66  tff(u150,negated_conjecture,
% 2.32/0.66      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 2.32/0.66  
% 2.32/0.66  tff(u149,axiom,
% 2.32/0.66      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 2.32/0.66  
% 2.32/0.66  tff(u148,axiom,
% 2.32/0.66      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 2.32/0.66  
% 2.32/0.66  tff(u147,negated_conjecture,
% 2.32/0.66      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 2.32/0.66  
% 2.32/0.66  tff(u146,negated_conjecture,
% 2.32/0.66      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 2.32/0.66  
% 2.32/0.66  tff(u145,axiom,
% 2.32/0.66      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 2.32/0.66  
% 2.32/0.66  tff(u144,axiom,
% 2.32/0.66      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 2.32/0.66  
% 2.32/0.66  tff(u143,negated_conjecture,
% 2.32/0.66      ((~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 2.32/0.66  
% 2.32/0.66  tff(u142,negated_conjecture,
% 2.32/0.66      ((~~v2_waybel_0(sK2,sK1)) | ~v2_waybel_0(sK2,sK1))).
% 2.32/0.66  
% 2.32/0.66  tff(u141,negated_conjecture,
% 2.32/0.66      ((~v2_waybel_0(sK2,sK0)) | v2_waybel_0(sK2,sK0))).
% 2.32/0.66  
% 2.32/0.66  % (9015)# SZS output end Saturation.
% 2.32/0.66  % (9015)------------------------------
% 2.32/0.66  % (9015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.66  % (9015)Termination reason: Satisfiable
% 2.32/0.66  
% 2.32/0.66  % (9015)Memory used [KB]: 10746
% 2.32/0.66  % (9015)Time elapsed: 0.209 s
% 2.32/0.66  % (9015)------------------------------
% 2.32/0.66  % (9015)------------------------------
% 2.32/0.66  % (8992)Success in time 0.301 s
%------------------------------------------------------------------------------
