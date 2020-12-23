%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  56 expanded)
%              Number of leaves         :   56 (  56 expanded)
%              Depth                    :    0
%              Number of atoms          :  141 ( 141 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2017)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
tff(u187,negated_conjecture,(
    l1_orders_2(sK5) )).

tff(u186,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP4(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u185,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP2(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u184,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,sK8)
        | r1_orders_2(sK5,X0,sK6) ) )).

% (2013)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
tff(u183,negated_conjecture,(
    m1_subset_1(sK6,u1_struct_0(sK5)) )).

tff(u182,negated_conjecture,(
    m1_subset_1(sK7,u1_struct_0(sK5)) )).

tff(u181,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) )).

tff(u180,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) )).

tff(u179,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK5,X0,sK6)
      | sP1(sK6,sK5,X0) ) )).

tff(u178,negated_conjecture,(
    ! [X1] :
      ( ~ r1_lattice3(sK5,X1,sK7)
      | sP1(sK7,sK5,X1) ) )).

tff(u177,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK9(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP1(X4,X5,X6)
      | sP1(sK9(X4,X5,X6),X5,X7) ) )).

tff(u176,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK10(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP3(X4,X5,X6)
      | sP1(sK10(X4,X5,X6),X5,X7) ) )).

tff(u175,negated_conjecture,
    ( ~ ~ r2_hidden(sK6,sK8)
    | ~ r2_hidden(sK6,sK8) )).

tff(u174,negated_conjecture,
    ( ~ ~ r2_hidden(sK7,sK8)
    | ~ r2_hidden(sK7,sK8) )).

tff(u173,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | ! [X0] :
        ( ~ r2_hidden(sK10(sK6,sK5,X0),sK8)
        | sP3(sK6,sK5,X0) ) )).

tff(u172,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) )).

tff(u171,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) )).

tff(u170,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
      | sP1(X0,X1,X2) ) )).

tff(u169,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK10(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) )).

tff(u168,negated_conjecture,
    ( ~ ~ r1_orders_2(sK5,sK6,sK6)
    | ~ r1_orders_2(sK5,sK6,sK6) )).

tff(u167,negated_conjecture,
    ( ~ ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK7,sK6) )).

tff(u166,negated_conjecture,(
    r1_orders_2(sK5,sK6,sK7) )).

tff(u165,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | ! [X1,X0] :
        ( r1_orders_2(sK5,sK9(X0,sK5,X1),sK6)
        | ~ r2_hidden(sK9(X0,sK5,X1),sK8)
        | sP1(X0,sK5,X1) ) )).

tff(u164,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | ! [X3,X2] :
        ( r1_orders_2(sK5,sK10(X2,sK5,X3),sK6)
        | ~ r2_hidden(sK10(X2,sK5,X3),sK8)
        | sP3(X2,sK5,X3) ) )).

tff(u163,negated_conjecture,
    ( ~ ~ r2_lattice3(sK5,sK8,sK7)
    | ~ r2_lattice3(sK5,sK8,sK7) )).

tff(u162,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK5,X0,sK6)
      | sP3(sK6,sK5,X0) ) )).

tff(u161,negated_conjecture,(
    ! [X1] :
      ( ~ r2_lattice3(sK5,X1,sK7)
      | sP3(sK7,sK5,X1) ) )).

tff(u160,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK9(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP1(X4,X5,X6)
      | sP3(sK9(X4,X5,X6),X5,X7) ) )).

tff(u159,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK10(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP3(X4,X5,X6)
      | sP3(sK10(X4,X5,X6),X5,X7) ) )).

tff(u158,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | r2_lattice3(sK5,sK8,sK6) )).

tff(u157,negated_conjecture,
    ( ~ ~ sP0(sK6,sK8,sK5,sK7)
    | ~ sP0(sK6,sK8,sK5,sK7) )).

tff(u156,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r1_lattice3(X2,X1,X0) ) )).

tff(u155,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_lattice3(X2,X1,X3) ) )).

tff(u154,negated_conjecture,(
    ! [X0] :
      ( ~ sP1(sK6,sK5,X0)
      | r1_lattice3(sK5,X0,sK6) ) )).

tff(u153,negated_conjecture,(
    ! [X1] :
      ( ~ sP1(sK7,sK5,X1)
      | r1_lattice3(sK5,X1,sK7) ) )).

tff(u152,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u151,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP1(sK9(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP1(X0,X1,X2)
      | r1_lattice3(X1,X3,sK9(X0,X1,X2)) ) )).

tff(u150,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP1(sK10(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP3(X0,X1,X2)
      | r1_lattice3(X1,X3,sK10(X0,X1,X2)) ) )).

tff(u149,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u148,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP2(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP1(X2,X1,X0) ) )).

tff(u147,negated_conjecture,(
    ! [X0] : sP2(X0,sK5,sK6) )).

tff(u146,negated_conjecture,(
    ! [X1] : sP2(X1,sK5,sK7) )).

tff(u145,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP2(X7,X5,sK9(X4,X5,X6))
      | sP1(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u144,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP2(X7,X5,sK10(X4,X5,X6))
      | sP3(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u143,negated_conjecture,(
    ! [X0] :
      ( ~ sP3(sK6,sK5,X0)
      | r2_lattice3(sK5,X0,sK6) ) )).

tff(u142,negated_conjecture,(
    ! [X1] :
      ( ~ sP3(sK7,sK5,X1)
      | r2_lattice3(sK5,X1,sK7) ) )).

tff(u141,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u140,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP3(sK9(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP1(X0,X1,X2)
      | r2_lattice3(X1,X3,sK9(X0,X1,X2)) ) )).

tff(u139,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP3(sK10(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP3(X0,X1,X2)
      | r2_lattice3(X1,X3,sK10(X0,X1,X2)) ) )).

tff(u138,negated_conjecture,
    ( ~ r2_lattice3(sK5,sK8,sK6)
    | sP3(sK6,sK5,sK8) )).

tff(u137,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u136,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP3(X2,X1,X0) ) )).

tff(u135,negated_conjecture,(
    ! [X0] : sP4(X0,sK5,sK6) )).

tff(u134,negated_conjecture,(
    ! [X1] : sP4(X1,sK5,sK7) )).

tff(u133,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP4(X3,X1,sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u132,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP4(X3,X1,sK10(X0,X1,X2))
      | sP3(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (2016)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.46  % (2016)Refutation not found, incomplete strategy% (2016)------------------------------
% 0.20/0.46  % (2016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (2016)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (2016)Memory used [KB]: 9850
% 0.20/0.46  % (2016)Time elapsed: 0.054 s
% 0.20/0.46  % (2016)------------------------------
% 0.20/0.46  % (2016)------------------------------
% 0.20/0.47  % (2025)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % (2014)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.47  % (2027)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (2027)Refutation not found, incomplete strategy% (2027)------------------------------
% 0.20/0.47  % (2027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (2027)Memory used [KB]: 5373
% 0.20/0.47  % (2027)Time elapsed: 0.063 s
% 0.20/0.47  % (2027)------------------------------
% 0.20/0.47  % (2027)------------------------------
% 0.20/0.48  % (2018)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (2031)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.48  % (2018)Refutation not found, incomplete strategy% (2018)------------------------------
% 0.20/0.48  % (2018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2018)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (2018)Memory used [KB]: 895
% 0.20/0.48  % (2018)Time elapsed: 0.072 s
% 0.20/0.48  % (2018)------------------------------
% 0.20/0.48  % (2018)------------------------------
% 0.20/0.48  % (2031)Refutation not found, incomplete strategy% (2031)------------------------------
% 0.20/0.48  % (2031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2031)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (2031)Memory used [KB]: 9850
% 0.20/0.48  % (2031)Time elapsed: 0.073 s
% 0.20/0.48  % (2031)------------------------------
% 0.20/0.48  % (2031)------------------------------
% 0.20/0.48  % (2024)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.48  % (2028)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (2020)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.49  % (2026)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (2028)Refutation not found, incomplete strategy% (2028)------------------------------
% 0.20/0.50  % (2028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2028)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2028)Memory used [KB]: 895
% 0.20/0.50  % (2028)Time elapsed: 0.055 s
% 0.20/0.50  % (2028)------------------------------
% 0.20/0.50  % (2028)------------------------------
% 0.20/0.50  % (2015)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.50  % (2033)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (2020)# SZS output start Saturation.
% 0.20/0.50  % (2017)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.50  tff(u187,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK5)).
% 0.20/0.50  
% 0.20/0.50  tff(u186,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP4(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u185,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP2(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u184,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK5)) | ~r2_hidden(X0,sK8) | r1_orders_2(sK5,X0,sK6)))))).
% 0.20/0.50  
% 0.20/0.50  % (2013)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.50  tff(u183,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK6,u1_struct_0(sK5))).
% 0.20/0.50  
% 0.20/0.50  tff(u182,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK7,u1_struct_0(sK5))).
% 0.20/0.50  
% 0.20/0.50  tff(u181,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | sP1(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u180,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u179,negated_conjecture,
% 0.20/0.50      (![X0] : ((~r1_lattice3(sK5,X0,sK6) | sP1(sK6,sK5,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u178,negated_conjecture,
% 0.20/0.50      (![X1] : ((~r1_lattice3(sK5,X1,sK7) | sP1(sK7,sK5,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u177,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK9(X4,X5,X6)) | ~l1_orders_2(X5) | sP1(X4,X5,X6) | sP1(sK9(X4,X5,X6),X5,X7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u176,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK10(X4,X5,X6)) | ~l1_orders_2(X5) | sP3(X4,X5,X6) | sP1(sK10(X4,X5,X6),X5,X7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u175,negated_conjecture,
% 0.20/0.50      ((~~r2_hidden(sK6,sK8)) | ~r2_hidden(sK6,sK8))).
% 0.20/0.50  
% 0.20/0.50  tff(u174,negated_conjecture,
% 0.20/0.50      ((~~r2_hidden(sK7,sK8)) | ~r2_hidden(sK7,sK8))).
% 0.20/0.50  
% 0.20/0.50  tff(u173,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | (![X0] : ((~r2_hidden(sK10(sK6,sK5,X0),sK8) | sP3(sK6,sK5,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u172,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK9(X0,X1,X2),X2) | sP1(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u171,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK10(X0,X1,X2),X2) | sP3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u170,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK9(X0,X1,X2)) | sP1(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u169,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,sK10(X0,X1,X2),X0) | sP3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u168,negated_conjecture,
% 0.20/0.50      ((~~r1_orders_2(sK5,sK6,sK6)) | ~r1_orders_2(sK5,sK6,sK6))).
% 0.20/0.50  
% 0.20/0.50  tff(u167,negated_conjecture,
% 0.20/0.50      ((~~r1_orders_2(sK5,sK7,sK6)) | ~r1_orders_2(sK5,sK7,sK6))).
% 0.20/0.50  
% 0.20/0.50  tff(u166,negated_conjecture,
% 0.20/0.50      r1_orders_2(sK5,sK6,sK7)).
% 0.20/0.50  
% 0.20/0.50  tff(u165,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | (![X1, X0] : ((r1_orders_2(sK5,sK9(X0,sK5,X1),sK6) | ~r2_hidden(sK9(X0,sK5,X1),sK8) | sP1(X0,sK5,X1)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u164,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | (![X3, X2] : ((r1_orders_2(sK5,sK10(X2,sK5,X3),sK6) | ~r2_hidden(sK10(X2,sK5,X3),sK8) | sP3(X2,sK5,X3)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u163,negated_conjecture,
% 0.20/0.50      ((~~r2_lattice3(sK5,sK8,sK7)) | ~r2_lattice3(sK5,sK8,sK7))).
% 0.20/0.50  
% 0.20/0.50  tff(u162,negated_conjecture,
% 0.20/0.50      (![X0] : ((~r2_lattice3(sK5,X0,sK6) | sP3(sK6,sK5,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u161,negated_conjecture,
% 0.20/0.50      (![X1] : ((~r2_lattice3(sK5,X1,sK7) | sP3(sK7,sK5,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u160,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK9(X4,X5,X6)) | ~l1_orders_2(X5) | sP1(X4,X5,X6) | sP3(sK9(X4,X5,X6),X5,X7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u159,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK10(X4,X5,X6)) | ~l1_orders_2(X5) | sP3(X4,X5,X6) | sP3(sK10(X4,X5,X6),X5,X7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u158,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | r2_lattice3(sK5,sK8,sK6))).
% 0.20/0.50  
% 0.20/0.50  tff(u157,negated_conjecture,
% 0.20/0.50      ((~~sP0(sK6,sK8,sK5,sK7)) | ~sP0(sK6,sK8,sK5,sK7))).
% 0.20/0.50  
% 0.20/0.50  tff(u156,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | ~r1_lattice3(X2,X1,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u155,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | r1_lattice3(X2,X1,X3))))).
% 0.20/0.50  
% 0.20/0.50  tff(u154,negated_conjecture,
% 0.20/0.50      (![X0] : ((~sP1(sK6,sK5,X0) | r1_lattice3(sK5,X0,sK6))))).
% 0.20/0.50  
% 0.20/0.50  tff(u153,negated_conjecture,
% 0.20/0.50      (![X1] : ((~sP1(sK7,sK5,X1) | r1_lattice3(sK5,X1,sK7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u152,axiom,
% 0.20/0.50      (![X1, X0, X2, X4] : ((~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.20/0.50  
% 0.20/0.50  tff(u151,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP1(sK9(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP1(X0,X1,X2) | r1_lattice3(X1,X3,sK9(X0,X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u150,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP1(sK10(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP3(X0,X1,X2) | r1_lattice3(X1,X3,sK10(X0,X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u149,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u148,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~sP2(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP1(X2,X1,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u147,negated_conjecture,
% 0.20/0.50      (![X0] : (sP2(X0,sK5,sK6)))).
% 0.20/0.50  
% 0.20/0.50  tff(u146,negated_conjecture,
% 0.20/0.50      (![X1] : (sP2(X1,sK5,sK7)))).
% 0.20/0.50  
% 0.20/0.50  tff(u145,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((sP2(X7,X5,sK9(X4,X5,X6)) | sP1(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.20/0.50  
% 0.20/0.50  tff(u144,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((sP2(X7,X5,sK10(X4,X5,X6)) | sP3(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.20/0.50  
% 0.20/0.50  tff(u143,negated_conjecture,
% 0.20/0.50      (![X0] : ((~sP3(sK6,sK5,X0) | r2_lattice3(sK5,X0,sK6))))).
% 0.20/0.50  
% 0.20/0.50  tff(u142,negated_conjecture,
% 0.20/0.50      (![X1] : ((~sP3(sK7,sK5,X1) | r2_lattice3(sK5,X1,sK7))))).
% 0.20/0.50  
% 0.20/0.50  tff(u141,axiom,
% 0.20/0.50      (![X1, X0, X2, X4] : ((~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u140,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP3(sK9(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP1(X0,X1,X2) | r2_lattice3(X1,X3,sK9(X0,X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u139,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~sP3(sK10(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP3(X0,X1,X2) | r2_lattice3(X1,X3,sK10(X0,X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u138,negated_conjecture,
% 0.20/0.50      ((~r2_lattice3(sK5,sK8,sK6)) | sP3(sK6,sK5,sK8))).
% 0.20/0.50  
% 0.20/0.50  tff(u137,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u136,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~sP4(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP3(X2,X1,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u135,negated_conjecture,
% 0.20/0.50      (![X0] : (sP4(X0,sK5,sK6)))).
% 0.20/0.50  
% 0.20/0.50  tff(u134,negated_conjecture,
% 0.20/0.50      (![X1] : (sP4(X1,sK5,sK7)))).
% 0.20/0.50  
% 0.20/0.50  tff(u133,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((sP4(X3,X1,sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u132,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((sP4(X3,X1,sK10(X0,X1,X2)) | sP3(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.20/0.50  
% 0.20/0.50  % (2020)# SZS output end Saturation.
% 0.20/0.50  % (2020)------------------------------
% 0.20/0.50  % (2020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2020)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (2020)Memory used [KB]: 5373
% 0.20/0.50  % (2020)Time elapsed: 0.059 s
% 0.20/0.50  % (2020)------------------------------
% 0.20/0.50  % (2020)------------------------------
% 0.20/0.50  % (2013)Refutation not found, incomplete strategy% (2013)------------------------------
% 0.20/0.50  % (2013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2013)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2013)Memory used [KB]: 5373
% 0.20/0.50  % (2013)Time elapsed: 0.092 s
% 0.20/0.50  % (2013)------------------------------
% 0.20/0.50  % (2013)------------------------------
% 0.20/0.50  % (2010)Success in time 0.145 s
%------------------------------------------------------------------------------
