%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   73 (  73 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u77,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) )).

tff(u76,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u75,axiom,(
    ! [X1,X0,X2] :
      ( v1_xboole_0(sK1(X1,X2,X0))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u74,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u73,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(sK1(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X2)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u72,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u71,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) )).

tff(u70,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u69,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
      | ~ r2_hidden(sK1(X1,X2,X0),X3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,X0)
      | r2_lattice3(X1,X2,X0) ) )).

tff(u67,axiom,(
    ! [X3,X5,X4,X6] :
      ( ~ m1_subset_1(sK1(X4,X6,X3),X5)
      | ~ l1_orders_2(X4)
      | ~ r2_lattice3(X4,X5,X3)
      | r2_lattice3(X4,X6,X3)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) )).

tff(u66,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u65,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u63,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u62,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r2_lattice3(X0,u1_struct_0(X0),X1)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )).

tff(u61,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_xboole_0(u1_struct_0(X0))
      | k1_xboole_0 = sK1(X0,X1,X2) ) )).

tff(u60,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_xboole_0(X2) ) )).

tff(u59,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u58,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X2) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:04:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (17657)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.47  % (17657)Refutation not found, incomplete strategy% (17657)------------------------------
% 0.22/0.47  % (17657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17657)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (17657)Memory used [KB]: 10490
% 0.22/0.47  % (17657)Time elapsed: 0.004 s
% 0.22/0.47  % (17657)------------------------------
% 0.22/0.47  % (17657)------------------------------
% 0.22/0.47  % (17665)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.48  % (17654)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (17654)Refutation not found, incomplete strategy% (17654)------------------------------
% 0.22/0.48  % (17654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17654)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (17654)Memory used [KB]: 6012
% 0.22/0.48  % (17654)Time elapsed: 0.001 s
% 0.22/0.48  % (17654)------------------------------
% 0.22/0.48  % (17654)------------------------------
% 0.22/0.49  % (17647)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (17652)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (17651)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (17669)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (17662)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (17649)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (17656)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (17663)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (17663)Refutation not found, incomplete strategy% (17663)------------------------------
% 0.22/0.51  % (17663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17663)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17663)Memory used [KB]: 1535
% 0.22/0.51  % (17663)Time elapsed: 0.001 s
% 0.22/0.51  % (17663)------------------------------
% 0.22/0.51  % (17663)------------------------------
% 0.22/0.51  % (17649)Refutation not found, incomplete strategy% (17649)------------------------------
% 0.22/0.51  % (17649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17649)Memory used [KB]: 10618
% 0.22/0.51  % (17649)Time elapsed: 0.094 s
% 0.22/0.51  % (17649)------------------------------
% 0.22/0.51  % (17649)------------------------------
% 0.22/0.51  % (17670)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (17653)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (17660)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (17670)Refutation not found, incomplete strategy% (17670)------------------------------
% 0.22/0.51  % (17670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17670)Memory used [KB]: 10618
% 0.22/0.51  % (17670)Time elapsed: 0.070 s
% 0.22/0.51  % (17670)------------------------------
% 0.22/0.51  % (17670)------------------------------
% 0.22/0.51  % (17664)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (17664)Refutation not found, incomplete strategy% (17664)------------------------------
% 0.22/0.51  % (17664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17664)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17664)Memory used [KB]: 1535
% 0.22/0.51  % (17664)Time elapsed: 0.099 s
% 0.22/0.51  % (17664)------------------------------
% 0.22/0.51  % (17664)------------------------------
% 0.22/0.51  % (17650)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (17650)Refutation not found, incomplete strategy% (17650)------------------------------
% 0.22/0.52  % (17650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17650)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17650)Memory used [KB]: 10490
% 0.22/0.52  % (17650)Time elapsed: 0.109 s
% 0.22/0.52  % (17650)------------------------------
% 0.22/0.52  % (17650)------------------------------
% 0.22/0.52  % (17668)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (17666)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (17666)Refutation not found, incomplete strategy% (17666)------------------------------
% 0.22/0.52  % (17666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17666)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17666)Memory used [KB]: 6140
% 0.22/0.52  % (17666)Time elapsed: 0.115 s
% 0.22/0.52  % (17666)------------------------------
% 0.22/0.52  % (17666)------------------------------
% 0.22/0.52  % (17659)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (17667)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (17658)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (17667)Refutation not found, incomplete strategy% (17667)------------------------------
% 0.22/0.52  % (17667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17667)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17667)Memory used [KB]: 6012
% 0.22/0.52  % (17667)Time elapsed: 0.109 s
% 0.22/0.52  % (17667)------------------------------
% 0.22/0.52  % (17667)------------------------------
% 0.22/0.52  % (17655)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (17653)Refutation not found, incomplete strategy% (17653)------------------------------
% 0.22/0.52  % (17653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17653)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17653)Memory used [KB]: 10618
% 0.22/0.52  % (17653)Time elapsed: 0.072 s
% 0.22/0.52  % (17653)------------------------------
% 0.22/0.52  % (17653)------------------------------
% 0.22/0.52  % (17647)Refutation not found, incomplete strategy% (17647)------------------------------
% 0.22/0.52  % (17647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17647)Memory used [KB]: 1663
% 0.22/0.52  % (17647)Time elapsed: 0.096 s
% 0.22/0.52  % (17647)------------------------------
% 0.22/0.52  % (17647)------------------------------
% 0.22/0.52  % (17655)Refutation not found, incomplete strategy% (17655)------------------------------
% 0.22/0.52  % (17655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17655)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17655)Memory used [KB]: 10490
% 0.22/0.52  % (17655)Time elapsed: 0.106 s
% 0.22/0.52  % (17655)------------------------------
% 0.22/0.52  % (17655)------------------------------
% 0.22/0.52  % (17648)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (17661)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (17665)Refutation not found, incomplete strategy% (17665)------------------------------
% 0.22/0.53  % (17665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17665)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17665)Memory used [KB]: 6012
% 0.22/0.53  % (17665)Time elapsed: 0.110 s
% 0.22/0.53  % (17665)------------------------------
% 0.22/0.53  % (17665)------------------------------
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (17659)# SZS output start Saturation.
% 0.22/0.54  tff(u77,axiom,
% 0.22/0.54      (![X0] : ((~v1_xboole_0(X0) | (k1_xboole_0 = X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u76,axiom,
% 0.22/0.54      v1_xboole_0(k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  tff(u75,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((v1_xboole_0(sK1(X1,X2,X0)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u74,axiom,
% 0.22/0.54      (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u73,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((~r2_hidden(sK1(X0,X1,X2),X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X3,X2) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u72,axiom,
% 0.22/0.54      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u71,axiom,
% 0.22/0.54      (![X1, X0] : ((r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u70,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u69,axiom,
% 0.22/0.54      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u68,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1)) | ~r2_hidden(sK1(X1,X2,X0),X3) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,X0) | r2_lattice3(X1,X2,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u67,axiom,
% 0.22/0.54      (![X3, X5, X4, X6] : ((~m1_subset_1(sK1(X4,X6,X3),X5) | ~l1_orders_2(X4) | ~r2_lattice3(X4,X5,X3) | r2_lattice3(X4,X6,X3) | v1_xboole_0(X5) | ~m1_subset_1(X3,u1_struct_0(X4)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u66,axiom,
% 0.22/0.54      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u65,axiom,
% 0.22/0.54      (![X1, X0] : ((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u64,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u63,negated_conjecture,
% 0.22/0.54      l1_orders_2(sK0)).
% 0.22/0.54  
% 0.22/0.54  tff(u62,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((r2_lattice3(X0,X2,X1) | ~r2_lattice3(X0,u1_struct_0(X0),X1) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u61,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v1_xboole_0(u1_struct_0(X0)) | (k1_xboole_0 = sK1(X0,X1,X2)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u60,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((r2_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_xboole_0(X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u59,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u58,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  % (17659)# SZS output end Saturation.
% 0.22/0.54  % (17659)------------------------------
% 0.22/0.54  % (17659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17659)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (17659)Memory used [KB]: 10618
% 0.22/0.54  % (17659)Time elapsed: 0.134 s
% 0.22/0.54  % (17659)------------------------------
% 0.22/0.54  % (17659)------------------------------
% 0.22/0.54  % (17646)Success in time 0.177 s
%------------------------------------------------------------------------------
