%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   48 (  48 expanded)
%              Depth                    :    0
%              Number of atoms          :  185 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u207,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r2_hidden(X2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X2) ) )).

tff(u206,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r2_hidden(X2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ r2_hidden(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X2) ) )).

tff(u205,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,X0) ) )).

tff(u204,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X5,X4,X6] :
        ( ~ r2_hidden(sK5(X4,X5,k4_waybel_0(sK2,sK3)),sK3)
        | sP0(X4,X5,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_orders_2(sK2,X6,sK5(X4,X5,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X6,X3)
        | ~ r1_orders_2(sK2,X3,sK4)
        | ~ m1_subset_1(X6,u1_struct_0(sK2)) ) )).

tff(u203,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X5,X7,X8,X6] :
        ( ~ r2_hidden(sK5(X6,X7,k4_waybel_0(sK2,sK3)),sK3)
        | ~ r2_hidden(X5,sK3)
        | sP0(X6,X7,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X5,sK4)
        | r1_orders_2(sK2,X8,sK5(X6,X7,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X8,X5)
        | ~ m1_subset_1(X8,u1_struct_0(sK2)) ) )).

tff(u202,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u201,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u200,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u199,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X3,X2,X4] :
        ( ~ m1_subset_1(sK5(X2,X3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,X3,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X2,X3,k4_waybel_0(sK2,sK3)),sK3)
        | r1_orders_2(sK2,X4,sK5(X2,X3,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X4,X1)
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) )).

tff(u198,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4)
        | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3)) ) )).

tff(u197,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ r2_hidden(X0,sK3)
        | ~ r1_orders_2(sK2,X0,sK4)
        | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3)) ) )).

tff(u196,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3)))
        | sP0(X0,X1,k4_waybel_0(sK2,sK3)) ) )).

tff(u195,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3) ) )).

tff(u194,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u193,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u192,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u191,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u190,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u189,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u188,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u187,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK2,sK5(X4,sK2,X5),sK4)
        | sP0(X4,sK2,X5)
        | ~ r2_hidden(X6,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X4,sK2,X5),X6) ) )).

tff(u186,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X3,X2] :
        ( ~ r1_orders_2(sK2,X3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,sK2,k4_waybel_0(sK2,sK3))
        | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )).

tff(u185,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3)))
        | sP0(X0,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u184,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( r1_orders_2(sK2,sK4,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X1,X2,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u183,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ r2_hidden(X0,sK3)
        | sP0(X1,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u182,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(X1,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u181,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X2,sK4)
        | ~ r2_hidden(X2,sK3)
        | sP0(X3,X4,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u180,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X2,sK4)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | sP0(X3,X4,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u179,negated_conjecture,
    ( ~ ~ r1_lattice3(sK2,sK3,sK4)
    | ~ r1_lattice3(sK2,sK3,sK4) )).

tff(u178,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u177,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_lattice3(sK2,X1,X2)
      | sP0(X2,sK2,X1)
      | ~ r2_hidden(X2,sK3) ) )).

tff(u176,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u175,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4) )).

tff(u174,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X0)
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ r2_hidden(X0,sK3) ) )).

tff(u173,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X4] :
        ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X3,sK2,X4))
        | sP0(X3,sK2,X4)
        | ~ r1_orders_2(sK2,sK5(X3,sK2,X4),sK4) ) )).

tff(u172,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r1_lattice3(sK2,X0,sK4) ) )).

tff(u171,negated_conjecture,(
    ! [X1,X2] :
      ( ~ sP0(X1,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_hidden(X1,sK3) ) )).

tff(u170,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u169,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u168,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)) )).

tff(u167,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( sP0(X0,sK2,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(X0,sK3)
        | ~ r1_orders_2(sK2,X0,sK4) ) )).

tff(u166,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( sP0(X0,sK2,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4) ) )).

tff(u165,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2] :
        ( sP0(sK5(X2,sK2,X3),sK2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,sK5(X2,sK2,X3),sK4)
        | sP0(X2,sK2,X3) ) )).

tff(u164,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u163,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u162,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u161,negated_conjecture,(
    ! [X1,X0] :
      ( sP1(X1,sK2,X0)
      | ~ r2_hidden(X0,sK3) ) )).

tff(u160,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (31154)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.46  % (31151)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (31146)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (31151)Refutation not found, incomplete strategy% (31151)------------------------------
% 0.20/0.46  % (31151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (31150)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (31151)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (31151)Memory used [KB]: 5373
% 0.20/0.46  % (31151)Time elapsed: 0.005 s
% 0.20/0.46  % (31151)------------------------------
% 0.20/0.46  % (31151)------------------------------
% 0.20/0.47  % (31143)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (31137)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.48  % (31154)Refutation not found, incomplete strategy% (31154)------------------------------
% 0.20/0.48  % (31154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31154)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31154)Memory used [KB]: 9850
% 0.20/0.48  % (31154)Time elapsed: 0.066 s
% 0.20/0.48  % (31154)------------------------------
% 0.20/0.48  % (31154)------------------------------
% 0.20/0.48  % (31142)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (31142)Refutation not found, incomplete strategy% (31142)------------------------------
% 0.20/0.48  % (31142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31142)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31142)Memory used [KB]: 895
% 0.20/0.48  % (31142)Time elapsed: 0.074 s
% 0.20/0.48  % (31142)------------------------------
% 0.20/0.48  % (31142)------------------------------
% 0.20/0.48  % (31141)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (31139)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  % (31138)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.49  % (31149)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (31144)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (31144)# SZS output start Saturation.
% 0.20/0.49  tff(u207,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r2_hidden(X2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u206,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r2_hidden(X2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X1,sK4) | ~r2_hidden(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u205,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,X0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u204,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X5, X4, X6] : ((~r2_hidden(sK5(X4,X5,k4_waybel_0(sK2,sK3)),sK3) | sP0(X4,X5,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_orders_2(sK2,X6,sK5(X4,X5,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X6,X3) | ~r1_orders_2(sK2,X3,sK4) | ~m1_subset_1(X6,u1_struct_0(sK2))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u203,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X5, X7, X8, X6] : ((~r2_hidden(sK5(X6,X7,k4_waybel_0(sK2,sK3)),sK3) | ~r2_hidden(X5,sK3) | sP0(X6,X7,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X5,sK4) | r1_orders_2(sK2,X8,sK5(X6,X7,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X8,X5) | ~m1_subset_1(X8,u1_struct_0(sK2))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u202,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.20/0.49  
% 0.20/0.49  tff(u201,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u200,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u199,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X3, X2, X4] : ((~m1_subset_1(sK5(X2,X3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,X3,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X2,X3,k4_waybel_0(sK2,sK3)),sK3) | r1_orders_2(sK2,X4,sK5(X2,X3,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X4,X1) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X4,u1_struct_0(sK2))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u198,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0, X2] : ((~m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u197,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0, X2] : ((~m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~r2_hidden(X0,sK3) | ~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u196,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3))) | sP0(X0,X1,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u195,negated_conjecture,
% 0.20/0.49      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u194,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.20/0.49  
% 0.20/0.49  tff(u193,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.20/0.49  
% 0.20/0.49  tff(u192,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.20/0.49  
% 0.20/0.49  tff(u191,negated_conjecture,
% 0.20/0.49      v4_orders_2(sK2)).
% 0.20/0.49  
% 0.20/0.49  tff(u190,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK2)).
% 0.20/0.49  
% 0.20/0.49  tff(u189,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.20/0.49  
% 0.20/0.49  tff(u188,axiom,
% 0.20/0.49      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u187,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X5, X4, X6] : ((~r1_orders_2(sK2,sK5(X4,sK2,X5),sK4) | sP0(X4,sK2,X5) | ~r2_hidden(X6,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X6,u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X4,sK2,X5),X6)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u186,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X3, X2] : ((~r1_orders_2(sK2,X3,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,sK2,k4_waybel_0(sK2,sK3)) | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X3,u1_struct_0(sK2))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u185,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3))) | sP0(X0,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u184,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((r1_orders_2(sK2,sK4,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X1,X2,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u183,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X0,sK4) | ~r2_hidden(X0,sK3) | sP0(X1,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u182,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(X1,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u181,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X2,sK4) | ~r2_hidden(X2,sK3) | sP0(X3,X4,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u180,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK2)) | sP0(X3,X4,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u179,negated_conjecture,
% 0.20/0.49      ((~~r1_lattice3(sK2,sK3,sK4)) | ~r1_lattice3(sK2,sK3,sK4))).
% 0.20/0.49  
% 0.20/0.49  tff(u178,negated_conjecture,
% 0.20/0.49      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u177,negated_conjecture,
% 0.20/0.49      (![X1, X2] : ((~r1_lattice3(sK2,X1,X2) | sP0(X2,sK2,X1) | ~r2_hidden(X2,sK3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u176,axiom,
% 0.20/0.49      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.20/0.49  
% 0.20/0.49  tff(u175,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4))).
% 0.20/0.49  
% 0.20/0.49  tff(u174,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X0) | ~r1_orders_2(sK2,X0,sK4) | ~r2_hidden(X0,sK3)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u173,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X4] : ((r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X3,sK2,X4)) | sP0(X3,sK2,X4) | ~r1_orders_2(sK2,sK5(X3,sK2,X4),sK4)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u172,negated_conjecture,
% 0.20/0.49      (![X0] : ((~sP0(sK4,sK2,X0) | r1_lattice3(sK2,X0,sK4))))).
% 0.20/0.49  
% 0.20/0.49  tff(u171,negated_conjecture,
% 0.20/0.49      (![X1, X2] : ((~sP0(X1,sK2,X2) | r1_lattice3(sK2,X2,X1) | ~r2_hidden(X1,sK3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u170,axiom,
% 0.20/0.49      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.20/0.49  
% 0.20/0.49  tff(u169,axiom,
% 0.20/0.49      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u168,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)))).
% 0.20/0.49  
% 0.20/0.49  tff(u167,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((sP0(X0,sK2,k4_waybel_0(sK2,sK3)) | ~r2_hidden(X0,sK3) | ~r1_orders_2(sK2,X0,sK4)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u166,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((sP0(X0,sK2,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u165,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2] : ((sP0(sK5(X2,sK2,X3),sK2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,sK5(X2,sK2,X3),sK4) | sP0(X2,sK2,X3)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u164,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.20/0.49  
% 0.20/0.49  tff(u163,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u162,negated_conjecture,
% 0.20/0.49      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.20/0.49  
% 0.20/0.49  tff(u161,negated_conjecture,
% 0.20/0.49      (![X1, X0] : ((sP1(X1,sK2,X0) | ~r2_hidden(X0,sK3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u160,axiom,
% 0.20/0.49      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.20/0.49  
% 0.20/0.49  % (31144)# SZS output end Saturation.
% 0.20/0.49  % (31144)------------------------------
% 0.20/0.49  % (31144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31144)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (31144)Memory used [KB]: 5373
% 0.20/0.49  % (31144)Time elapsed: 0.081 s
% 0.20/0.49  % (31144)------------------------------
% 0.20/0.49  % (31144)------------------------------
% 0.20/0.49  % (31136)Success in time 0.132 s
%------------------------------------------------------------------------------
