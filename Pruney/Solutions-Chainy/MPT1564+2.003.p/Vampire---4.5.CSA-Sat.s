%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   87 (  87 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u92,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u91,axiom,(
    ! [X9,X7,X8] :
      ( v1_xboole_0(sK3(X7,X8,X9))
      | sP0(X7,X8,X9)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) )).

tff(u90,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u89,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u88,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u87,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u86,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u85,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2)
      | v1_xboole_0(X2) ) )).

tff(u84,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u83,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u82,axiom,(
    ! [X5,X4,X6] :
      ( r2_hidden(sK3(X4,X5,X6),u1_struct_0(X5))
      | sP0(X4,X5,X6)
      | v1_xboole_0(u1_struct_0(X5)) ) )).

tff(u81,negated_conjecture,(
    ~ v2_struct_0(sK2) )).

tff(u80,negated_conjecture,(
    l1_struct_0(sK2) )).

tff(u79,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u78,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sP0(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u76,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK3(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK3(X4,X5,X6),X5,X7) ) )).

tff(u75,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X4,X7,sK3(X5,X6,u1_struct_0(X4)))
      | sP0(X5,X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | v1_xboole_0(u1_struct_0(X4))
      | sP0(sK3(X5,X6,u1_struct_0(X4)),X4,X7) ) )).

tff(u74,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK3(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u73,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u72,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u71,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK3(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK3(X0,X1,X2)) ) )).

tff(u70,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK3(X1,X2,u1_struct_0(X0)),X0,X3)
      | sP0(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r1_lattice3(X0,X3,sK3(X1,X2,u1_struct_0(X0))) ) )).

tff(u69,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u68,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u67,axiom,(
    ! [X1,X0,X2] :
      ( sP1(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u66,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u65,axiom,(
    ! [X9,X7,X8,X6] :
      ( sP1(X9,X8,sK3(X6,X7,u1_struct_0(X8)))
      | v1_xboole_0(u1_struct_0(X8))
      | sP0(X6,X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2509)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.46  % (2502)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.47  % (2509)Refutation not found, incomplete strategy% (2509)------------------------------
% 0.21/0.47  % (2509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2509)Memory used [KB]: 9850
% 0.21/0.47  % (2509)Time elapsed: 0.053 s
% 0.21/0.47  % (2509)------------------------------
% 0.21/0.47  % (2509)------------------------------
% 0.21/0.47  % (2502)Refutation not found, incomplete strategy% (2502)------------------------------
% 0.21/0.47  % (2502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2502)Memory used [KB]: 9850
% 0.21/0.47  % (2502)Time elapsed: 0.052 s
% 0.21/0.47  % (2502)------------------------------
% 0.21/0.47  % (2502)------------------------------
% 0.21/0.48  % (2500)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (2517)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.48  % (2518)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (2501)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (2514)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (2517)Refutation not found, incomplete strategy% (2517)------------------------------
% 0.21/0.48  % (2517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2517)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2517)Memory used [KB]: 9850
% 0.21/0.48  % (2517)Time elapsed: 0.031 s
% 0.21/0.48  % (2517)------------------------------
% 0.21/0.48  % (2517)------------------------------
% 0.21/0.48  % (2514)Refutation not found, incomplete strategy% (2514)------------------------------
% 0.21/0.48  % (2514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2514)Memory used [KB]: 5373
% 0.21/0.48  % (2514)Time elapsed: 0.068 s
% 0.21/0.48  % (2514)------------------------------
% 0.21/0.48  % (2514)------------------------------
% 0.21/0.48  % (2504)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (2515)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (2515)Refutation not found, incomplete strategy% (2515)------------------------------
% 0.21/0.48  % (2515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2515)Memory used [KB]: 895
% 0.21/0.48  % (2515)Time elapsed: 0.029 s
% 0.21/0.48  % (2515)------------------------------
% 0.21/0.48  % (2515)------------------------------
% 0.21/0.48  % (2510)WARNING: option uwaf not known.
% 0.21/0.48  % (2505)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (2510)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % (2505)Refutation not found, incomplete strategy% (2505)------------------------------
% 0.21/0.49  % (2505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2505)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2505)Memory used [KB]: 895
% 0.21/0.49  % (2505)Time elapsed: 0.077 s
% 0.21/0.49  % (2505)------------------------------
% 0.21/0.49  % (2505)------------------------------
% 0.21/0.49  % (2510)Refutation not found, incomplete strategy% (2510)------------------------------
% 0.21/0.49  % (2510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2510)Memory used [KB]: 895
% 0.21/0.49  % (2510)Time elapsed: 0.072 s
% 0.21/0.49  % (2510)------------------------------
% 0.21/0.49  % (2510)------------------------------
% 0.21/0.49  % (2499)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (2512)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (2499)Refutation not found, incomplete strategy% (2499)------------------------------
% 0.21/0.49  % (2499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2499)Memory used [KB]: 5373
% 0.21/0.49  % (2499)Time elapsed: 0.075 s
% 0.21/0.49  % (2499)------------------------------
% 0.21/0.49  % (2499)------------------------------
% 0.21/0.49  % (2516)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.49  % (2513)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (2516)Refutation not found, incomplete strategy% (2516)------------------------------
% 0.21/0.49  % (2516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2516)Memory used [KB]: 5373
% 0.21/0.49  % (2516)Time elapsed: 0.087 s
% 0.21/0.49  % (2516)------------------------------
% 0.21/0.49  % (2516)------------------------------
% 0.21/0.49  % (2511)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.49  % (2520)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.49  % (2507)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (2507)# SZS output start Saturation.
% 0.21/0.50  tff(u92,axiom,
% 0.21/0.50      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u91,axiom,
% 0.21/0.50      (![X9, X7, X8] : ((v1_xboole_0(sK3(X7,X8,X9)) | sP0(X7,X8,X9) | ~v1_xboole_0(u1_struct_0(X8)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u90,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u89,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u88,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u87,axiom,
% 0.21/0.50      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u86,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u85,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2) | v1_xboole_0(X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u84,axiom,
% 0.21/0.50      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u83,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u82,axiom,
% 0.21/0.50      (![X5, X4, X6] : ((r2_hidden(sK3(X4,X5,X6),u1_struct_0(X5)) | sP0(X4,X5,X6) | v1_xboole_0(u1_struct_0(X5)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u81,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u80,negated_conjecture,
% 0.21/0.50      l1_struct_0(sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u79,axiom,
% 0.21/0.50      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u78,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u77,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | sP0(X2,X0,X1) | ~l1_orders_2(X0) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u76,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK3(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK3(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u75,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X4,X7,sK3(X5,X6,u1_struct_0(X4))) | sP0(X5,X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | v1_xboole_0(u1_struct_0(X4)) | sP0(sK3(X5,X6,u1_struct_0(X4)),X4,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u74,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK3(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u73,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP0(X0,X1,X2) | r1_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | ~v1_xboole_0(X0) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u72,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u71,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK3(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK3(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u70,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK3(X1,X2,u1_struct_0(X0)),X0,X3) | sP0(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | r1_lattice3(X0,X3,sK3(X1,X2,u1_struct_0(X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u69,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u68,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u67,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((sP1(X0,X1,X2) | ~l1_orders_2(X1) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u66,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u65,axiom,
% 0.21/0.50      (![X9, X7, X8, X6] : ((sP1(X9,X8,sK3(X6,X7,u1_struct_0(X8))) | v1_xboole_0(u1_struct_0(X8)) | sP0(X6,X7,u1_struct_0(X8)) | ~l1_orders_2(X8))))).
% 0.21/0.50  
% 0.21/0.50  % (2507)# SZS output end Saturation.
% 0.21/0.50  % (2507)------------------------------
% 0.21/0.50  % (2507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2507)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (2507)Memory used [KB]: 5373
% 0.21/0.50  % (2507)Time elapsed: 0.073 s
% 0.21/0.50  % (2507)------------------------------
% 0.21/0.50  % (2507)------------------------------
% 0.21/0.50  % (2495)Success in time 0.138 s
%------------------------------------------------------------------------------
