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
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u70,negated_conjecture,
    ( ~ ( sK1 != k13_lattice3(sK0,sK1,sK2) )
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

tff(u69,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) )).

tff(u68,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) )).

tff(u67,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) )).

tff(u66,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u65,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u64,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u63,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u62,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u61,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u60,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u59,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u58,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u57,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u55,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u54,negated_conjecture,(
    v1_lattice3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (21808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (21808)Refutation not found, incomplete strategy% (21808)------------------------------
% 0.20/0.50  % (21808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21808)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21808)Memory used [KB]: 10618
% 0.20/0.50  % (21808)Time elapsed: 0.086 s
% 0.20/0.50  % (21808)------------------------------
% 0.20/0.50  % (21808)------------------------------
% 0.20/0.51  % (21809)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (21817)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (21817)Refutation not found, incomplete strategy% (21817)------------------------------
% 0.20/0.51  % (21817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21817)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21817)Memory used [KB]: 1663
% 0.20/0.51  % (21817)Time elapsed: 0.072 s
% 0.20/0.51  % (21817)------------------------------
% 0.20/0.51  % (21817)------------------------------
% 0.20/0.51  % (21822)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (21822)Refutation not found, incomplete strategy% (21822)------------------------------
% 0.20/0.52  % (21822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21822)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21822)Memory used [KB]: 1535
% 0.20/0.52  % (21822)Time elapsed: 0.089 s
% 0.20/0.52  % (21822)------------------------------
% 0.20/0.52  % (21822)------------------------------
% 0.20/0.52  % (21813)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (21825)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (21820)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.52  % (21825)Refutation not found, incomplete strategy% (21825)------------------------------
% 0.20/0.52  % (21825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21825)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21825)Memory used [KB]: 6140
% 0.20/0.52  % (21825)Time elapsed: 0.099 s
% 0.20/0.52  % (21825)------------------------------
% 0.20/0.52  % (21825)------------------------------
% 0.20/0.52  % (21813)Refutation not found, incomplete strategy% (21813)------------------------------
% 0.20/0.52  % (21813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21813)Memory used [KB]: 10618
% 0.20/0.52  % (21813)Time elapsed: 0.087 s
% 0.20/0.52  % (21813)------------------------------
% 0.20/0.52  % (21813)------------------------------
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (21820)# SZS output start Saturation.
% 0.20/0.52  tff(u70,negated_conjecture,
% 0.20/0.52      ((~(sK1 != k13_lattice3(sK0,sK1,sK2))) | (sK1 != k13_lattice3(sK0,sK1,sK2)))).
% 0.20/0.52  
% 0.20/0.52  tff(u69,axiom,
% 0.20/0.52      (![X1, X0] : ((~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u68,axiom,
% 0.20/0.52      (![X1, X0] : ((~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u67,axiom,
% 0.20/0.52      (![X0] : ((~v1_xboole_0(X0) | (k1_xboole_0 = X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u66,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u65,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u64,axiom,
% 0.20/0.52      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u63,axiom,
% 0.20/0.52      (![X1, X0] : ((r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u62,axiom,
% 0.20/0.52      (![X0] : ((~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u61,negated_conjecture,
% 0.20/0.52      l1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  tff(u60,axiom,
% 0.20/0.52      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u59,negated_conjecture,
% 0.20/0.52      l1_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  tff(u58,negated_conjecture,
% 0.20/0.52      v3_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  tff(u57,negated_conjecture,
% 0.20/0.52      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.20/0.52  
% 0.20/0.52  tff(u56,axiom,
% 0.20/0.52      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u55,negated_conjecture,
% 0.20/0.52      v5_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  tff(u54,negated_conjecture,
% 0.20/0.52      v1_lattice3(sK0)).
% 0.20/0.52  
% 0.20/0.52  % (21820)# SZS output end Saturation.
% 0.20/0.52  % (21820)------------------------------
% 0.20/0.52  % (21820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21820)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (21820)Memory used [KB]: 10618
% 0.20/0.52  % (21820)Time elapsed: 0.060 s
% 0.20/0.52  % (21820)------------------------------
% 0.20/0.52  % (21820)------------------------------
% 0.20/0.52  % (21810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.52  % (21819)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.53  % (21799)Success in time 0.169 s
%------------------------------------------------------------------------------
