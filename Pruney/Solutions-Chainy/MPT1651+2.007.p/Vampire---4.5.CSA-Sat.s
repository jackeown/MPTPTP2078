%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:06 EST 2020

% Result     : CounterSatisfiable 0.55s
% Output     : Saturation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   82 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u116,negated_conjecture,(
    ~ v2_struct_0(sK2) )).

tff(u115,negated_conjecture,(
    v3_orders_2(sK2) )).

tff(u114,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u113,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u111,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,X1,k3_waybel_0(sK2,sK3)) ) )).

tff(u110,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u105,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r1_orders_2(sK2,X1,sK5(X2,sK2,k3_waybel_0(sK2,sK3)))
        | r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u104,negated_conjecture,(
    r1_orders_2(sK2,sK4,sK4) )).

tff(u103,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) )).

tff(u101,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u100,negated_conjecture,
    ( ~ ~ r2_lattice3(sK2,sK3,sK4)
    | ~ r2_lattice3(sK2,sK3,sK4) )).

tff(u99,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u98,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u97,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4) )).

tff(u96,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK4) ) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u94,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r2_lattice3(sK2,X0,sK4) ) )).

tff(u93,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u92,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u91,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u89,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u88,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u87,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (727842816)
% 0.14/0.37  ipcrm: permission denied for id (727973893)
% 0.22/0.37  ipcrm: permission denied for id (728072200)
% 0.22/0.38  ipcrm: permission denied for id (728104969)
% 0.22/0.38  ipcrm: permission denied for id (728170507)
% 0.22/0.38  ipcrm: permission denied for id (728203276)
% 0.22/0.38  ipcrm: permission denied for id (728236045)
% 0.22/0.38  ipcrm: permission denied for id (728268814)
% 0.22/0.38  ipcrm: permission denied for id (728367120)
% 0.22/0.39  ipcrm: permission denied for id (728432658)
% 0.22/0.39  ipcrm: permission denied for id (728465427)
% 0.22/0.39  ipcrm: permission denied for id (728498196)
% 0.22/0.39  ipcrm: permission denied for id (728563735)
% 0.22/0.41  ipcrm: permission denied for id (728891427)
% 0.22/0.41  ipcrm: permission denied for id (728924196)
% 0.22/0.41  ipcrm: permission denied for id (728956965)
% 0.22/0.41  ipcrm: permission denied for id (728989735)
% 0.22/0.42  ipcrm: permission denied for id (729120813)
% 0.22/0.42  ipcrm: permission denied for id (729153582)
% 0.22/0.43  ipcrm: permission denied for id (729317427)
% 0.22/0.43  ipcrm: permission denied for id (729350196)
% 0.22/0.43  ipcrm: permission denied for id (729382965)
% 0.22/0.44  ipcrm: permission denied for id (729612350)
% 0.22/0.44  ipcrm: permission denied for id (729645119)
% 0.22/0.44  ipcrm: permission denied for id (729677888)
% 0.22/0.44  ipcrm: permission denied for id (729710657)
% 0.22/0.45  ipcrm: permission denied for id (729874503)
% 0.22/0.45  ipcrm: permission denied for id (729940041)
% 0.22/0.46  ipcrm: permission denied for id (729972810)
% 0.22/0.46  ipcrm: permission denied for id (730005579)
% 0.22/0.46  ipcrm: permission denied for id (730038348)
% 0.22/0.46  ipcrm: permission denied for id (730071117)
% 0.22/0.47  ipcrm: permission denied for id (730169426)
% 0.22/0.47  ipcrm: permission denied for id (730234964)
% 0.22/0.47  ipcrm: permission denied for id (730366041)
% 0.22/0.48  ipcrm: permission denied for id (730398810)
% 0.22/0.48  ipcrm: permission denied for id (730431580)
% 0.22/0.48  ipcrm: permission denied for id (730529889)
% 0.22/0.49  ipcrm: permission denied for id (730562662)
% 0.22/0.50  ipcrm: permission denied for id (730660971)
% 0.22/0.50  ipcrm: permission denied for id (730726510)
% 0.22/0.50  ipcrm: permission denied for id (730792047)
% 0.22/0.50  ipcrm: permission denied for id (730824816)
% 0.22/0.51  ipcrm: permission denied for id (730890356)
% 0.22/0.51  ipcrm: permission denied for id (730923126)
% 0.22/0.51  ipcrm: permission denied for id (730988664)
% 0.22/0.52  ipcrm: permission denied for id (731054205)
% 0.22/0.52  ipcrm: permission denied for id (731086974)
% 0.39/0.59  % (2557)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.39/0.60  % (2557)Refutation not found, incomplete strategy% (2557)------------------------------
% 0.39/0.60  % (2557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.60  % (2557)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.60  
% 0.39/0.60  % (2557)Memory used [KB]: 5373
% 0.39/0.60  % (2557)Time elapsed: 0.027 s
% 0.39/0.60  % (2557)------------------------------
% 0.39/0.60  % (2557)------------------------------
% 0.39/0.62  % (2573)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.39/0.62  % (2573)Refutation not found, incomplete strategy% (2573)------------------------------
% 0.39/0.62  % (2573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.62  % (2573)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.62  
% 0.39/0.62  % (2573)Memory used [KB]: 5373
% 0.39/0.62  % (2573)Time elapsed: 0.005 s
% 0.39/0.62  % (2573)------------------------------
% 0.39/0.62  % (2573)------------------------------
% 0.55/0.64  % (2567)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.55/0.64  % (2567)Refutation not found, incomplete strategy% (2567)------------------------------
% 0.55/0.64  % (2567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.64  % (2567)Termination reason: Refutation not found, incomplete strategy
% 0.55/0.64  
% 0.55/0.64  % (2567)Memory used [KB]: 9850
% 0.55/0.64  % (2567)Time elapsed: 0.068 s
% 0.55/0.64  % (2567)------------------------------
% 0.55/0.64  % (2567)------------------------------
% 0.55/0.65  % (2563)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.55/0.65  % (2579)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.55/0.66  % (2576)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.55/0.66  % (2566)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.55/0.66  % (2576)Refutation not found, incomplete strategy% (2576)------------------------------
% 0.55/0.66  % (2576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.66  % (2576)Termination reason: Refutation not found, incomplete strategy
% 0.55/0.66  
% 0.55/0.66  % (2576)Memory used [KB]: 9850
% 0.55/0.66  % (2576)Time elapsed: 0.026 s
% 0.55/0.66  % (2576)------------------------------
% 0.55/0.66  % (2576)------------------------------
% 0.55/0.66  % (2559)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.55/0.67  % (2560)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.55/0.67  % (2574)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.55/0.67  % (2574)Refutation not found, incomplete strategy% (2574)------------------------------
% 0.55/0.67  % (2574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.67  % (2574)Termination reason: Refutation not found, incomplete strategy
% 0.55/0.67  
% 0.55/0.67  % (2574)Memory used [KB]: 895
% 0.55/0.67  % (2574)Time elapsed: 0.112 s
% 0.55/0.67  % (2574)------------------------------
% 0.55/0.67  % (2574)------------------------------
% 0.55/0.67  % (2577)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.55/0.67  % (2560)Refutation not found, incomplete strategy% (2560)------------------------------
% 0.55/0.67  % (2560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.67  % (2560)Termination reason: Refutation not found, incomplete strategy
% 0.55/0.67  
% 0.55/0.67  % (2560)Memory used [KB]: 9850
% 0.55/0.67  % (2560)Time elapsed: 0.082 s
% 0.55/0.67  % (2560)------------------------------
% 0.55/0.67  % (2560)------------------------------
% 0.55/0.67  % (2564)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.55/0.67  % SZS status CounterSatisfiable for theBenchmark
% 0.55/0.67  % (2564)# SZS output start Saturation.
% 0.55/0.67  tff(u116,negated_conjecture,
% 0.55/0.67      ~v2_struct_0(sK2)).
% 0.55/0.67  
% 0.55/0.67  tff(u115,negated_conjecture,
% 0.55/0.67      v3_orders_2(sK2)).
% 0.55/0.67  
% 0.55/0.67  tff(u114,negated_conjecture,
% 0.55/0.67      l1_orders_2(sK2)).
% 0.55/0.67  
% 0.55/0.67  tff(u113,axiom,
% 0.55/0.67      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u112,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u111,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,X1,k3_waybel_0(sK2,sK3))))))).
% 0.55/0.67  
% 0.55/0.67  tff(u110,negated_conjecture,
% 0.55/0.67      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.55/0.67  
% 0.55/0.67  tff(u109,negated_conjecture,
% 0.55/0.67      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.55/0.67  
% 0.55/0.67  tff(u108,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.55/0.67  
% 0.55/0.67  tff(u107,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.55/0.67  
% 0.55/0.67  tff(u106,axiom,
% 0.55/0.67      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u105,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r1_orders_2(sK2,X1,sK5(X2,sK2,k3_waybel_0(sK2,sK3))) | r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.55/0.67  
% 0.55/0.67  tff(u104,negated_conjecture,
% 0.55/0.67      r1_orders_2(sK2,sK4,sK4)).
% 0.55/0.67  
% 0.55/0.67  tff(u103,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.55/0.67  
% 0.55/0.67  tff(u102,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | sP0(X1,X0,X2))))).
% 0.55/0.67  
% 0.55/0.67  tff(u101,negated_conjecture,
% 0.55/0.67      v4_orders_2(sK2)).
% 0.55/0.67  
% 0.55/0.67  tff(u100,negated_conjecture,
% 0.55/0.67      ((~~r2_lattice3(sK2,sK3,sK4)) | ~r2_lattice3(sK2,sK3,sK4))).
% 0.55/0.67  
% 0.55/0.67  tff(u99,negated_conjecture,
% 0.55/0.67      (![X0] : ((~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u98,axiom,
% 0.55/0.67      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.55/0.67  
% 0.55/0.67  tff(u97,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4))).
% 0.55/0.67  
% 0.55/0.67  tff(u96,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4)))))).
% 0.55/0.67  
% 0.55/0.67  tff(u95,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.55/0.67  
% 0.55/0.67  tff(u94,negated_conjecture,
% 0.55/0.67      (![X0] : ((~sP0(sK4,sK2,X0) | r2_lattice3(sK2,X0,sK4))))).
% 0.55/0.67  
% 0.55/0.67  tff(u93,axiom,
% 0.55/0.67      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u92,axiom,
% 0.55/0.67      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.55/0.67  
% 0.55/0.67  tff(u91,negated_conjecture,
% 0.55/0.67      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)))).
% 0.55/0.67  
% 0.55/0.67  tff(u90,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.55/0.67  
% 0.55/0.67  tff(u89,axiom,
% 0.55/0.67      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.55/0.67  
% 0.55/0.67  tff(u88,negated_conjecture,
% 0.55/0.67      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.55/0.67  
% 0.55/0.67  tff(u87,axiom,
% 0.55/0.67      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.55/0.67  
% 0.55/0.67  % (2564)# SZS output end Saturation.
% 0.55/0.67  % (2564)------------------------------
% 0.55/0.67  % (2564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.67  % (2564)Termination reason: Satisfiable
% 0.55/0.67  
% 0.55/0.67  % (2564)Memory used [KB]: 5373
% 0.55/0.67  % (2564)Time elapsed: 0.084 s
% 0.55/0.67  % (2564)------------------------------
% 0.55/0.67  % (2564)------------------------------
% 0.55/0.67  % (2413)Success in time 0.313 s
%------------------------------------------------------------------------------
