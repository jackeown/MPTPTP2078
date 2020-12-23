%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u62,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u61,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u60,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u59,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u58,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u57,axiom,(
    ! [X5,X4,X6] :
      ( r2_hidden(sK3(X4,X5,X6),u1_struct_0(X5))
      | v1_xboole_0(u1_struct_0(X5))
      | sP0(X4,X5,X6) ) )).

tff(u56,negated_conjecture,(
    ~ v2_struct_0(sK2) )).

tff(u55,negated_conjecture,(
    l1_struct_0(sK2) )).

tff(u54,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u53,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u52,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK3(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK3(X4,X5,X6),X5,X7) ) )).

tff(u51,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK3(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u49,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK3(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK3(X0,X1,X2)) ) )).

tff(u48,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u47,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u46,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:02:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (2586)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (2584)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (2595)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (2593)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.51  % (2585)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.51  % (2583)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.51  % (2585)Refutation not found, incomplete strategy% (2585)------------------------------
% 0.21/0.51  % (2585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2585)Memory used [KB]: 9850
% 0.21/0.51  % (2585)Time elapsed: 0.092 s
% 0.21/0.51  % (2585)------------------------------
% 0.21/0.51  % (2585)------------------------------
% 0.21/0.51  % (2582)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (2582)Refutation not found, incomplete strategy% (2582)------------------------------
% 0.21/0.51  % (2582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2582)Memory used [KB]: 5245
% 0.21/0.51  % (2582)Time elapsed: 0.091 s
% 0.21/0.51  % (2582)------------------------------
% 0.21/0.51  % (2582)------------------------------
% 0.21/0.51  % (2589)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (2589)# SZS output start Saturation.
% 0.21/0.51  tff(u62,axiom,
% 0.21/0.51      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u61,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u60,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u59,axiom,
% 0.21/0.51      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u58,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u57,axiom,
% 0.21/0.51      (![X5, X4, X6] : ((r2_hidden(sK3(X4,X5,X6),u1_struct_0(X5)) | v1_xboole_0(u1_struct_0(X5)) | sP0(X4,X5,X6))))).
% 0.21/0.51  
% 0.21/0.51  tff(u56,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK2)).
% 0.21/0.51  
% 0.21/0.51  tff(u55,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK2)).
% 0.21/0.51  
% 0.21/0.51  tff(u54,axiom,
% 0.21/0.51      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u53,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK2)).
% 0.21/0.51  
% 0.21/0.51  tff(u52,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK3(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK3(X4,X5,X6),X5,X7))))).
% 0.21/0.51  
% 0.21/0.51  tff(u51,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK3(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u50,axiom,
% 0.21/0.51      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.51  
% 0.21/0.51  tff(u49,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~sP0(sK3(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK3(X0,X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u48,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u47,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u46,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.51  
% 0.21/0.51  % (2589)# SZS output end Saturation.
% 0.21/0.51  % (2589)------------------------------
% 0.21/0.51  % (2589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2589)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (2589)Memory used [KB]: 5373
% 0.21/0.51  % (2589)Time elapsed: 0.101 s
% 0.21/0.51  % (2589)------------------------------
% 0.21/0.51  % (2589)------------------------------
% 0.21/0.51  % (2591)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (2579)Success in time 0.154 s
%------------------------------------------------------------------------------
