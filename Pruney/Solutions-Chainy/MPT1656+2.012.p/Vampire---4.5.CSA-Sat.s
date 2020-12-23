%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  62 expanded)
%              Number of leaves         :   62 (  62 expanded)
%              Depth                    :    0
%              Number of atoms          :  202 ( 202 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u217,negated_conjecture,(
    ~ v2_struct_0(sK4) )).

tff(u216,negated_conjecture,(
    v3_orders_2(sK4) )).

tff(u215,negated_conjecture,(
    l1_orders_2(sK4) )).

tff(u214,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u213,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u212,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u211,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5)))
        | sP0(X0,X1,k4_waybel_0(sK4,sK5)) ) )).

tff(u210,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( ~ m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5)))
        | sP2(X2,X3,k4_waybel_0(sK4,sK5)) ) )).

tff(u209,negated_conjecture,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) )).

tff(u208,negated_conjecture,(
    m1_subset_1(sK6,u1_struct_0(sK4)) )).

tff(u207,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u206,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) )).

tff(u205,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u204,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK8(X0,X1,X2))
      | sP2(X0,X1,X2) ) )).

tff(u203,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4] :
        ( ~ r1_orders_2(sK4,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X5)
        | ~ r1_orders_2(sK4,X4,sK6)
        | ~ m1_subset_1(X5,u1_struct_0(sK4)) ) )).

tff(u202,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK4,sK7(X2,sK4,X3),sK6)
        | sP0(X2,sK4,X3)
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X4)
        | ~ r1_orders_2(sK4,X4,sK7(X2,sK4,X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK4)) ) )).

tff(u201,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK4,sK7(X2,sK4,X3),sK6)
        | sP0(X2,sK4,X3)
        | ~ r2_hidden(X4,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK7(X2,sK4,X3),X4) ) )).

tff(u200,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK4,sK8(X2,sK4,X3),sK6)
        | sP2(X2,sK4,X3)
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X4)
        | ~ r1_orders_2(sK4,X4,sK8(X2,sK4,X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK4)) ) )).

tff(u199,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK4,sK8(X2,sK4,X3),sK6)
        | sP2(X2,sK4,X3)
        | ~ r2_hidden(X4,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK8(X2,sK4,X3),X4) ) )).

tff(u198,negated_conjecture,(
    r1_orders_2(sK4,sK6,sK6) )).

tff(u197,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP0(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u196,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP2(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u195,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK7(X1,X0,X2),sK7(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) )).

tff(u194,axiom,(
    ! [X3,X5,X4] :
      ( r1_orders_2(X3,sK8(X4,X3,X5),sK8(X4,X3,X5))
      | ~ l1_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | sP2(X4,X3,X5) ) )).

tff(u193,negated_conjecture,
    ( ~ ~ r1_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) )).

tff(u192,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK4,X0,sK6)
      | sP2(sK6,sK4,X0) ) )).

tff(u191,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP2(sK7(X4,X5,X6),X5,X7) ) )).

tff(u190,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP2(sK8(X4,X5,X6),X5,X7) ) )).

tff(u189,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u188,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0)
        | ~ r1_orders_2(sK4,X0,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) ) )).

tff(u187,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6) )).

tff(u186,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK7(X0,sK4,X1))
        | ~ r1_orders_2(sK4,sK7(X0,sK4,X1),sK6)
        | sP0(X0,sK4,X1) ) )).

tff(u185,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK8(X0,sK4,X1))
        | ~ r1_orders_2(sK4,sK8(X0,sK4,X1),sK6)
        | sP2(X0,sK4,X1) ) )).

tff(u184,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,X0) ) )).

tff(u183,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u182,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u181,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK4,X0,sK6)
      | sP0(sK6,sK4,X0) ) )).

tff(u180,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK7(X4,X5,X6),X5,X7) ) )).

tff(u179,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP0(sK8(X4,X5,X6),X5,X7) ) )).

tff(u178,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u177,negated_conjecture,(
    v4_orders_2(sK4) )).

tff(u176,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u175,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK6,sK4,X0)
      | r2_lattice3(sK4,X0,sK6) ) )).

tff(u174,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u173,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r2_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u172,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u171,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u170,negated_conjecture,(
    ! [X0] : sP1(X0,sK4,sK6) )).

tff(u169,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK7(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u168,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK8(X4,X5,X6))
      | sP2(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u167,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u166,negated_conjecture,(
    ! [X0] :
      ( ~ sP2(sK6,sK4,X0)
      | r1_lattice3(sK4,X0,sK6) ) )).

tff(u165,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u164,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r1_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u163,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)) )).

tff(u162,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( sP2(sK7(X0,sK4,X1),sK4,k4_waybel_0(sK4,sK5))
        | sP0(X0,sK4,X1)
        | ~ r1_orders_2(sK4,sK7(X0,sK4,X1),sK6) ) )).

tff(u161,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( sP2(sK8(X2,sK4,X3),sK4,k4_waybel_0(sK4,sK5))
        | sP2(X2,sK4,X3)
        | ~ r1_orders_2(sK4,sK8(X2,sK4,X3),sK6) ) )).

tff(u160,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u159,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) )).

tff(u158,negated_conjecture,(
    ! [X0] : sP3(X0,sK4,sK6) )).

tff(u157,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK7(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

% (7049)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
tff(u156,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK8(X0,X1,X2))
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (7040)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (7042)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (7042)Refutation not found, incomplete strategy% (7042)------------------------------
% 0.21/0.47  % (7042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7042)Memory used [KB]: 5373
% 0.21/0.47  % (7042)Time elapsed: 0.052 s
% 0.21/0.47  % (7042)------------------------------
% 0.21/0.47  % (7042)------------------------------
% 0.21/0.47  % (7032)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (7033)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (7028)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (7034)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (7041)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (7029)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.49  % (7036)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (7031)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.49  % (7031)Refutation not found, incomplete strategy% (7031)------------------------------
% 0.21/0.49  % (7031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7031)Memory used [KB]: 9850
% 0.21/0.49  % (7031)Time elapsed: 0.076 s
% 0.21/0.49  % (7031)------------------------------
% 0.21/0.49  % (7031)------------------------------
% 0.21/0.49  % (7043)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (7043)Refutation not found, incomplete strategy% (7043)------------------------------
% 0.21/0.49  % (7043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7043)Memory used [KB]: 895
% 0.21/0.49  % (7043)Time elapsed: 0.044 s
% 0.21/0.49  % (7043)------------------------------
% 0.21/0.49  % (7043)------------------------------
% 0.21/0.50  % (7035)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (7035)# SZS output start Saturation.
% 0.21/0.50  tff(u217,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u216,negated_conjecture,
% 0.21/0.50      v3_orders_2(sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u215,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u214,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u213,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u212,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u211,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((~m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5))) | sP0(X0,X1,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u210,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((~m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5))) | sP2(X2,X3,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u209,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))).
% 0.21/0.50  
% 0.21/0.50  tff(u208,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK6,u1_struct_0(sK4))).
% 0.21/0.50  
% 0.21/0.50  tff(u207,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u206,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u205,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,sK7(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u204,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK8(X0,X1,X2)) | sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u203,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4] : ((~r1_orders_2(sK4,X5,X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X5) | ~r1_orders_2(sK4,X4,sK6) | ~m1_subset_1(X5,u1_struct_0(sK4))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u202,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((~r1_orders_2(sK4,sK7(X2,sK4,X3),sK6) | sP0(X2,sK4,X3) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X4) | ~r1_orders_2(sK4,X4,sK7(X2,sK4,X3)) | ~m1_subset_1(X4,u1_struct_0(sK4))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u201,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((~r1_orders_2(sK4,sK7(X2,sK4,X3),sK6) | sP0(X2,sK4,X3) | ~r2_hidden(X4,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_orders_2(sK4,sK7(X2,sK4,X3),X4)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u200,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((~r1_orders_2(sK4,sK8(X2,sK4,X3),sK6) | sP2(X2,sK4,X3) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X4) | ~r1_orders_2(sK4,X4,sK8(X2,sK4,X3)) | ~m1_subset_1(X4,u1_struct_0(sK4))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u199,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((~r1_orders_2(sK4,sK8(X2,sK4,X3),sK6) | sP2(X2,sK4,X3) | ~r2_hidden(X4,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_orders_2(sK4,sK8(X2,sK4,X3),X4)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u198,negated_conjecture,
% 0.21/0.50      r1_orders_2(sK4,sK6,sK6)).
% 0.21/0.50  
% 0.21/0.50  tff(u197,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5))) | sP0(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u196,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5))) | sP2(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u195,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r1_orders_2(X0,sK7(X1,X0,X2),sK7(X1,X0,X2)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | sP0(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u194,axiom,
% 0.21/0.50      (![X3, X5, X4] : ((r1_orders_2(X3,sK8(X4,X3,X5),sK8(X4,X3,X5)) | ~l1_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3) | sP2(X4,X3,X5))))).
% 0.21/0.50  
% 0.21/0.50  tff(u193,negated_conjecture,
% 0.21/0.50      ((~~r1_lattice3(sK4,sK5,sK6)) | ~r1_lattice3(sK4,sK5,sK6))).
% 0.21/0.50  
% 0.21/0.50  tff(u192,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r1_lattice3(sK4,X0,sK6) | sP2(sK6,sK4,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u191,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP2(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u190,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP2(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u189,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u188,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0) | ~r1_orders_2(sK4,X0,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u187,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6))).
% 0.21/0.50  
% 0.21/0.50  tff(u186,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK7(X0,sK4,X1)) | ~r1_orders_2(sK4,sK7(X0,sK4,X1),sK6) | sP0(X0,sK4,X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u185,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK8(X0,sK4,X1)) | ~r1_orders_2(sK4,sK8(X0,sK4,X1),sK6) | sP2(X0,sK4,X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u184,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u183,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u182,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK8(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u181,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r2_lattice3(sK4,X0,sK6) | sP0(sK6,sK4,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u180,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u179,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP0(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u178,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u177,negated_conjecture,
% 0.21/0.50      v4_orders_2(sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u176,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u175,negated_conjecture,
% 0.21/0.50      (![X0] : ((~sP0(sK6,sK4,X0) | r2_lattice3(sK4,X0,sK6))))).
% 0.21/0.50  
% 0.21/0.50  tff(u174,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u173,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r2_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u172,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u171,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u170,negated_conjecture,
% 0.21/0.50      (![X0] : (sP1(X0,sK4,sK6)))).
% 0.21/0.50  
% 0.21/0.50  tff(u169,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK7(X4,X5,X6)) | sP0(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.50  
% 0.21/0.50  tff(u168,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK8(X4,X5,X6)) | sP2(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.50  
% 0.21/0.50  tff(u167,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u166,negated_conjecture,
% 0.21/0.50      (![X0] : ((~sP2(sK6,sK4,X0) | r1_lattice3(sK4,X0,sK6))))).
% 0.21/0.50  
% 0.21/0.50  tff(u165,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP2(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u164,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP2(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r1_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u163,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)))).
% 0.21/0.50  
% 0.21/0.50  tff(u162,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((sP2(sK7(X0,sK4,X1),sK4,k4_waybel_0(sK4,sK5)) | sP0(X0,sK4,X1) | ~r1_orders_2(sK4,sK7(X0,sK4,X1),sK6)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u161,negated_conjecture,
% 0.21/0.50      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((sP2(sK8(X2,sK4,X3),sK4,k4_waybel_0(sK4,sK5)) | sP2(X2,sK4,X3) | ~r1_orders_2(sK4,sK8(X2,sK4,X3),sK6)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u160,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u159,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP2(X2,X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u158,negated_conjecture,
% 0.21/0.50      (![X0] : (sP3(X0,sK4,sK6)))).
% 0.21/0.50  
% 0.21/0.50  tff(u157,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK7(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.50  
% 0.21/0.50  % (7049)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.50  tff(u156,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK8(X0,X1,X2)) | sP2(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.50  
% 0.21/0.50  % (7035)# SZS output end Saturation.
% 0.21/0.50  % (7035)------------------------------
% 0.21/0.50  % (7035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7035)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (7035)Memory used [KB]: 5373
% 0.21/0.50  % (7035)Time elapsed: 0.057 s
% 0.21/0.50  % (7035)------------------------------
% 0.21/0.50  % (7035)------------------------------
% 0.21/0.50  % (7038)WARNING: option uwaf not known.
% 0.21/0.50  % (7025)Success in time 0.137 s
%------------------------------------------------------------------------------
